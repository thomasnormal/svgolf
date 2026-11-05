#!/usr/bin/env python3.12
"""Flow A1' (WP-X1): the canonical RTLIL of the pinned flow (score/canon.ys output) mapped by `abc -liberty` onto
sky130_fd_sc_hd with a FIXED cell policy (sky130.py: DONT_USE), a fixed ABC script and fixed constraints.
This module only runs Yosys; sky_a1.py measures.

Variants (all with the same dont_use list unless said):
  u      the Yosys 0.53 default script for -liberty (no -constr), written out explicitly
         strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; &get -n; &dch -f; &nf; &put
  u0     the same by omission (no -script): must be byte-identical to u (checked)
  s      u + `-constr` (driver buf_1, PO load 10 fF) + buffer; upsize; dnsize; stime -p   (ABC's sizing)
  f      Yosys `-fast`: strash; dretime; map
  l      light:  strash; &get -n; &dch -f; &nf; &put
  h      heavy:  strash; resyn2 x2 (explicit); &get -n; &dch -f; &nf; &put
  r      u on the 2-input + mux sub-library (no compound AOI/OAI/MAJ/3-4-input cells): the compound-cell gain
"""
import os, re, subprocess, sys, tempfile, time

import fetch_sky130
import sky130 as S
import sky130_designs as SD

DEFAULT = "strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; &get -n; &dch -f; &nf; &put"
RESYN2 = ("balance; rewrite; refactor; balance; rewrite; rewrite -z; balance; refactor -z; rewrite -z; balance")
SCRIPTS = {
    "u": DEFAULT,
    "s": "strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; &get -n; &dch -f; &nf {D}; &put; buffer; upsize {D}; dnsize {D}; stime -p",
    "l": "strash; &get -n; &dch -f; &nf; &put",
    "h": f"strash; {RESYN2}; {RESYN2}; &get -n; &dch -f; &nf; &put",
    "r": DEFAULT,
}
# the 2-input + MUX sub-library: everything of class "logic" that is not one of these families is also dont_use
SIMPLE_KEEP = ("inv_", "buf_", "nand2_", "nor2_", "and2_", "or2_", "xor2_", "xnor2_", "mux2_",
               "nand2b_", "nor2b_", "and2b_", "or2b_")
CONSTR = os.path.join(SD.D.HERE, "data", "sky130", "abc.constr")


def simple_dont_use(lib):
    out = []
    for n in sorted(lib._cells):
        if S.cell_class(n)[0] != "logic":
            continue
        if not S.short(n).startswith(SIMPLE_KEEP):
            out.append(n)
    return out


def write_constr():
    os.makedirs(os.path.dirname(CONSTR), exist_ok=True)
    with open(CONSTR, "w") as fh:
        fh.write(f"set_driving_cell {S.PREFIX}buf_1\nset_load {S.PO_LOAD_PF * 1000:g}\n")
    return CONSTR


def ys_script(rtlil, top, out_v, variant, libp, extra_dont_use=(), tie=True, D=None):
    dont = S.dont_use_args() + "".join(f" -dont_use {n}" for n in extra_dont_use)
    if variant == "u0":
        abc = f"abc -liberty {libp} {dont}"
    elif variant == "f":
        abc = f"abc -fast -liberty {libp} {dont}"
    elif variant == "s0":      # the same by omission of -script (Yosys's own -constr default): must equal "s"
        abc = f"abc -liberty {libp} {dont} -constr {write_constr()}" + (f" -D {D}" if D else "")
    elif variant == "s":
        abc = (f"abc -liberty {libp} {dont} -constr {write_constr()}" + (f" -D {D}" if D else "")
               + f" -script +{SCRIPTS['s'].replace(' ', ',')}")
    else:
        abc = f"abc -liberty {libp} {dont} -script +{SCRIPTS[variant].replace(' ', ',')}"
    # constants: a tie cell per constant bit, counted as a cell (none of the studied designs has one)
    hilo = (f"hilomap -hicell {S.PREFIX}conb_1 HI -locell {S.PREFIX}conb_1 LO\n" if tie else "")
    return (f"read_rtlil {rtlil}\nsynth -flatten -top {top}\n{abc}\nopt_clean -purge\n{hilo}"
            f"tee -q -o {out_v}.stat stat -liberty {libp}\nwrite_verilog -noattr -noexpr {out_v}\n")


def run(rtlil, top, out_v, variant="u", lib=None, env=None, timeout=1800, D=None):
    """Map; returns dict(seconds, abc_stime_ps, stat_area, cmd). The netlist is out_v, the log out_v + '.log'."""
    libp = fetch_sky130.lib_path()
    extra = simple_dont_use(lib) if variant == "r" else ()
    os.makedirs(os.path.dirname(out_v), exist_ok=True)
    ys = out_v + ".ys"
    with open(ys, "w") as fh:
        fh.write(ys_script(rtlil, top, out_v, variant, libp, extra, True, D))
    t = time.time()
    r = subprocess.run(["yosys", "-q", "-l", out_v + ".log", ys], capture_output=True, text=True, timeout=timeout,
                       env=env or dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
    dt = time.time() - t
    if r.returncode != 0:
        raise RuntimeError(r.stderr[-1500:] + r.stdout[-1500:])
    log = open(out_v + ".log").read()
    sm = re.findall(r"Delay =\s+([\d.]+) ps", log)
    st = open(out_v + ".stat").read()
    m = re.search(r"Chip area for (?:top )?module '[^']*': ([\d.]+)", st)
    return {"seconds": dt, "abc_stime_ps": float(sm[-1]) if sm else None, "stat_area_um2": float(m.group(1)) if m else None}
