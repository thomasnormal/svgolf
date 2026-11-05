"""Measurement of one sky130-cell netlist under the study's fixed setup (WP-X1): area in um^2 and GE, cell count and
histogram, unit depth, NLDM delay T (ps), critical path, and optionally activity-only and glitch-aware energy.
Pure functions over WP-X0's engine; nothing here reads Yosys."""
import collections

import engine as E
import netlist as N
import sky130 as S
import vectors


def build(nl_cells, lib):
    return E.Design(nl_cells, lib)


def static(d, lib, pi_slew=S.PI_SLEW_NS, po_load=S.PO_LOAD_PF):
    t, path, _ = d.sta_nldm(pi_slew, po_load)
    area = d.area_um2()
    hist = d.cell_counts()
    sh = {S.short(k): v for k, v in hist.items()}
    nbuf = sum(v for k, v in sh.items() if k.startswith(("buf_", "bufbuf_", "bufinv_")))
    ninv = sum(v for k, v in sh.items() if k.startswith("inv_"))
    compound = sum(v for k, v in sh.items() if k.split("_")[0].rstrip("0123456789") in
                   ("a21oi", "o21ai", "a21o", "o21a", "a22oi", "a22o", "o22ai", "o22a", "a211oi", "o211ai", "a31oi", "o31ai",
                    "a21boi", "o21bai", "a2bb2oi", "o2bb2ai", "maj3", "mux2i", "a221oi", "o221ai", "a32oi", "o32ai", "a41oi", "o41ai",
                    "a311oi", "o311ai", "a2111oi", "o2111ai", "a211o", "o211a", "a221o", "o221a", "a222oi", "a31o", "o31a", "a311o", "o311a",
                    "a32o", "o32a", "a41o", "o41a", "a2111o", "o2111a", "a2bb2o", "o2bb2a", "a21bo", "o21ba", "o221a"))
    return {"area_um2": round(area, 4), "area_ge": round(area / S.NAND2_UM2, 3), "cells": sum(hist.values()),
            "hist": sh, "n_buf": nbuf, "n_inv": ninv, "n_compound": compound, "n_mux": sum(v for k, v in sh.items() if k.startswith("mux")),
            "unit_depth": d.unit_depth(), "t_ps": round(t * 1000, 2), "t_ns": t,
            "crit_cells": [S.short(d.cells[i].name) for i in _crit_gates(d, path)]}


def _crit_gates(d, path):
    """Gate indices along the critical path (path = [(net, edge, arrival)])."""
    out = []
    for net, e, _ in path[1:]:
        if net in d.driver:
            out.append(d.driver[net][0])
    return out


def energy(d, nl_pi, nvec=2001, seed=1, pairs=0, pi_slew=S.PI_SLEW_NS, po_load=S.PO_LOAD_PF, t_ns=None):
    """Activity-only (zero-delay) energy per operation over nvec-1 transitions of the pinned stream, and, when
    pairs > 0, the glitch-aware energy (inertial-delay event simulation, rise/fall delays from the STA) over the
    first `pairs` transitions. fJ per operation; leakage separate (nW * ns -> aJ -> fJ)."""
    if t_ns is None:
        t_ns, _, _ = d.sta_nldm(pi_slew, po_load)
    sim = E.Sim(d)
    pv = vectors.pi_values(nl_pi, nvec, seed)
    v = sim.run(pv, nvec)
    nets = [n for n in v if n not in ("0", "1")]
    tc = E.toggle_counts(v, nets, nvec)
    rises = {n: r / (nvec - 1) for n, (r, f) in tc.items()}
    falls = {n: f / (nvec - 1) for n, (r, f) in tc.items()}
    sw = S.switching_fj(d, rises, falls, po_load)
    it = S.internal_fj(d, rises, falls, pi_slew)
    out = {"e_sw_fj": sw, "e_int_fj": it, "e_act_fj": sw + it,
           "e_leak_fj": d.leakage_nw() * t_ns * 1e-3, "toggles_gate_outputs": sum(rises.get(n, 0) + falls.get(n, 0) for n in d.driver)}
    if pairs:
        tt, zz = E.timed_toggle_counts(d, v, nl_pi, nvec, pairs)
        tr = {n: tt[n][0] / pairs for n in tt}; tf = {n: tt[n][1] / pairs for n in tt}
        zr = {n: zz[n][0] / pairs for n in zz}; zf = {n: zz[n][1] / pairs for n in zz}
        eg = S.switching_fj(d, tr, tf, po_load) + S.internal_fj(d, tr, tf, pi_slew)
        ez = S.switching_fj(d, zr, zf, po_load) + S.internal_fj(d, zr, zf, pi_slew)
        out.update({"e_glitch_fj": eg, "e_act_same_pairs_fj": ez, "glitch_factor": eg / ez, "pairs": pairs})
    return out
