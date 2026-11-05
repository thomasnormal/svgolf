"""The design list of the PPA spike: (name, task, source path relative to svgolf/, top).

All sources are the existing references and baselines of tasks `add` and `mul`
(nothing new is written). `banned` marks the two Yosys-operator baselines
(`+`, `*`): scored with the banlist lifted, as in tests/expected.json.
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.abspath(os.path.join(HERE, "..", "..", ".."))

ADD = [
    ("add_ripple",   "tasks/add/reference/add_n.sv",             False),
    ("add_sklansky", "tests/add/baselines/add_n_sklansky.sv",    False),
    ("add_kogge",    "tests/add/baselines/add_n_kogge_stone.sv", False),
    ("add_cmpcarry", "tests/add/baselines/cmp_carry.sv",         False),
    ("add_yosys",    "tests/add/negative/plus.sv",               True),
]
MUL = [
    ("mul_array",    "tasks/mul/reference/mul_n.sv",             False),
    ("mul_tree",     "tasks/mul/reference/mul_tree.sv",          False),
    ("mul_wallace",  "tasks/mul/reference/mul_wallace.sv",       False),
    ("mul_tree_h",   "tasks/mul/reference/mul_tree_h.sv",        False),
    ("mul_dadda_rc", "tests/mul/baselines/dadda_rc_{N}.sv",      False),
    ("mul_dadda_ks", "tests/mul/baselines/dadda_ks_{N}.sv",      False),
    ("mul_yosys",    "tests/mul/baselines/yosys_mul.sv",         True),
]

def designs(task=None):
    out = []
    for name, src, banned in ADD:
        out.append(dict(name=name, task="add", src=src, top="add_n", banned=banned))
    for name, src, banned in MUL:
        out.append(dict(name=name, task="mul", src=src, top="mul_n", banned=banned))
    return [d for d in out if task in (None, d["task"])]
