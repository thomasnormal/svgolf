"""Verilog cell models for simulating a sky130-mapped netlist (WP-X1).

  generated_models(lib, cells)   one `module <cell>(ports); assign Y = <liberty function>; endmodule` per cell, ports
                                 named as in the liberty; no power pins, no specify block, no UDP, no timescale.
  upstream_wrappers(lib, cells)  thin wrapper modules `sky130_fd_sc_hd__nand2_1 -> sky130_fd_sc_hd__nand2` so the
                                 pinned upstream functional models (primitives + UDPs) can be used for any drive strength.
"""
import re
import sky130 as S


def vexpr(fn):
    """Liberty boolean function -> Verilog expression."""
    return fn.replace("!", "~")


def ports(c):
    return list(c.outputs) + list(c.inputs)


def generated_models(lib, cells):
    out = ["// generated from the liberty `function` strings of sky130_fd_sc_hd__tt_025C_1v80 (WP-X1)"]
    for n in sorted(cells):
        c = lib.cell(n)
        pl = ", ".join(ports(c))
        out.append(f"module {n}({pl});")
        out.append("  output " + ", ".join(c.outputs) + ";")
        out.append("  input " + ", ".join(c.inputs) + ";" if c.inputs else "")
        for o in c.outputs:
            out.append(f"  assign {o} = {vexpr(c.function[o])};")
        out.append("endmodule")
    return "\n".join(l for l in out if l != "") + "\n"


def upstream_wrappers(lib, cells):
    out = ["// drive-strength wrappers around the pinned upstream functional models (WP-X1)"]
    fam_of = lambda n: re.sub(r"_\d+$", "", n)
    for n in sorted(cells):
        c = lib.cell(n)
        pl = ", ".join(ports(c))
        out.append(f"module {n}({pl});")
        out.append("  output " + ", ".join(c.outputs) + ";")
        out.append("  input " + ", ".join(c.inputs) + ";" if c.inputs else "")
        conns = ", ".join(f".{p}({p})" for p in ports(c))
        out.append(f"  {fam_of(n)} base({conns});")
        out.append("endmodule")
    return "\n".join(l for l in out if l != "") + "\n"


def used_cells(netlist_path):
    txt = open(netlist_path).read()
    return sorted(set(re.findall(r"^\s*(sky130_fd_sc_hd__\w+)\s+\S+\s*\(", txt, re.M)))
