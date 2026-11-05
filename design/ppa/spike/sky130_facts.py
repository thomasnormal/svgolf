#!/usr/bin/env python3.12
"""Library facts of sky130_fd_sc_hd tt_025C_1v80 for the study (WP-X1): areas, the derived GE table against
score/ge.json, flip-flop and latch prices and timing, drive-strength spread, the units and sign convention of the
power tables, and the cell-policy census. Prints Markdown; writes data/sky130/facts.json.

  python3.12 sky130_facts.py
"""
import json, os, collections
import liberty as L
import sky130 as S, sky130_designs as SD

LIBP = lambda n: S.PREFIX + n
GE_JSON = os.path.join(SD.D.SVGOLF, "score", "ge.json")


def delay_ps(c, slew, load, rising_out=None):
    """Worst arc delay of a combinational cell at (input slew ns, load pF), ps; (rise, fall) maxima."""
    best = {"r": 0.0, "f": 0.0}
    for op in c.outputs:
        for arc in c.arcs[op]:
            if "cell_rise" in arc.tbl:
                best["r"] = max(best["r"], arc.tbl["cell_rise"].at(slew, load))
                best["f"] = max(best["f"], arc.tbl["cell_fall"].at(slew, load))
    return best["r"] * 1000, best["f"] * 1000


def groups(lib, name):
    return lib._cells[LIBP(name)]


def seq_timing(lib, name, clk_slew=0.05, d_slew=0.05, load=0.010):
    """clk->Q, setup, hold (ps) of a flip-flop / latch; None where the cell has no such arc."""
    g = groups(lib, name)
    out = {}
    for p in g.find("pin"):
        for t in p.find("timing"):
            tt = t.attrs.get("timing_type")
            related = t.attrs.get("related_pin")
            if tt in ("rising_edge", "falling_edge") or (tt == "clear") or (tt == "preset"):
                vals = []
                for k in ("cell_rise", "cell_fall"):
                    for c in t.find(k):
                        vals.append(L.Table(c).at(clk_slew, load) * 1000)
                if vals:
                    key = {"rising_edge": "clk_to_q", "falling_edge": "clk_to_q_neg", "clear": f"{related}_to_q", "preset": f"{related}_to_q"}[tt]
                    out[key] = max(out.get(key, 0), max(vals))
            elif tt and (tt.startswith("setup") or tt.startswith("hold") or tt.startswith("recovery") or tt.startswith("removal")):
                vals = []
                for k in ("rise_constraint", "fall_constraint"):
                    for c in t.find(k):
                        vals.append(L.Table(c).at(clk_slew, d_slew) * 1000)
                if vals:
                    key = tt.split("_")[0] + "_" + p.args[0]
                    out[key] = max(out.get(key, -1e9), max(vals))
    return out


def main():
    lib = S.load_lib()
    nand = lib.cell(LIBP("nand2_1")).area
    facts = {"lib": os.path.basename(S.fetch_sky130.lib_path()), "nand2_1_um2": nand}
    md = []
    P = md.append

    # ---------------------------------------------------------------- 1. area table
    P("### Areas, GE and pin capacitances of the relevant cells (um^2; GE = area / nand2_1; caps in fF)\n")
    P("| cell | area um^2 | GE | input caps fF | leakage nW (average) | function |\n|---|--:|--:|---|--:|---|")
    rel = "inv_1 buf_1 nand2_1 nor2_1 and2_1 or2_1 xor2_1 xnor2_1 mux2_1 nand2b_1 nor2b_1 and2b_1 or2b_1 nand3_1 nor3_1 a21oi_1 o21ai_1 a21o_1 o21a_1 a22oi_1 maj3_1 mux2i_1 fa_1 ha_1 conb_1 dfxtp_1 dfrtp_1 dfstp_1 dfbbp_1 dlxtp_1".split()
    rows = []
    for n in rel:
        c = lib.cell(LIBP(n))
        caps = ", ".join(f"{p} {v*1000:.2f}" for p, v in c.pin_cap.items() if p not in ("CLK", "GATE")) or "-"
        fn = ("; ".join(f"{o}={f}" for o, f in c.function.items()) if not c.is_seq else "sequential").replace("|", "\\|")
        P(f"| {n} | {c.area:.4f} | {c.area/nand:.3f} | {caps} | {c.leak:.4f} | {fn} |")
        rows.append(dict(cell=n, area=c.area, ge=round(c.area / nand, 4)))
    facts["relevant"] = rows

    # ---------------------------------------------------------------- 2. GE table
    ge = {k: v for k, v in json.load(open(GE_JSON)).items() if not k.startswith("_")}
    REAL = {"NOT": ["inv_1"], "BUF": ["buf_1"], "NAND": ["nand2_1"], "NOR": ["nor2_1"], "AND": ["and2_1"], "OR": ["or2_1"],
            "XOR": ["xor2_1"], "XNOR": ["xnor2_1"], "MUX": ["mux2_1"], "ANDNOT": ["nor2b_1"], "ORNOT": ["nand2b_1"]}
    P("\n### The GE table derived from sky130 against score/ge.json\n")
    P("| Yosys gate | sky130 cell | um^2 | derived GE | ge.json | derived / ge.json |\n|---|---|--:|--:|--:|--:|")
    tab = {}
    for k in sorted(REAL, key=lambda k: ge[k]):
        a = sum(lib.cell(LIBP(c)).area for c in REAL[k])
        d = a / nand
        tab[k] = dict(cells=REAL[k], um2=a, ge=round(d, 4), ge_json=ge[k])
        P(f"| {k} | {'+'.join(REAL[k])} | {a:.4f} | {d:.4f} | {ge[k]:.3f} | {(f'{d/ge[k]:.3f}' if ge[k] else 'n/a')} |")
    facts["ge_table"] = tab
    P("\nANDNOT / ORNOT alternatives: " + "; ".join(f"{k}: " + ", ".join(f"{c} {a/nand:.3f} GE" for c, a in v) for k, v in S.ANDNOT_ALT.items()))
    P("\nThe two inverter-like costs: inv_1 = %.4f um^2, inv_2 = %.4f, inv_4 = %.4f; clkinv_1 = %.4f; buf_1 = %.4f; nand2_2 = %.4f." % tuple(
        lib.cell(LIBP(n)).area for n in ("inv_1", "inv_2", "inv_4", "clkinv_1", "buf_1", "nand2_2")))

    # ---------------------------------------------------------------- 3. sequential
    P("\n### Flip-flops and latches: price and timing (clk slew 0.05 ns, data slew 0.05 ns, Q load 10 fF; ps)\n")
    P("| cell | um^2 | GE | clk->Q | setup D | hold D | async->Q | recovery | removal | notes |\n|---|--:|--:|--:|--:|--:|--:|--:|--:|---|")
    seq = {}
    for n, note in [("dfxtp_1", "plain D flip-flop"), ("dfxtp_2", ""), ("dfxtp_4", ""), ("dfxbp_1", "Q and Q_N"), ("dfrtp_1", "async reset (RESET_B)"),
                    ("dfrtp_2", ""), ("dfstp_1", "async set (SET_B)"), ("dfbbp_1", "async set and reset, Q and Q_N"), ("dfrbp_1", "async reset, Q and Q_N"),
                    ("edfxtp_1", "enable flop (mux inside)"), ("sdfxtp_1", "scan flop"), ("dlxtp_1", "latch, active-high gate"), ("dlxtn_1", "latch, active-low gate"),
                    ("dlrtp_1", "latch with reset"), ("dlclkp_1", "clock-gate latch")]:
        c = lib.cell(LIBP(n))
        st = seq_timing(lib, n)
        keys = list(st)
        setup = next((st[k] for k in keys if k.startswith("setup_D") or k.startswith("setup_DE")), None)
        hold = next((st[k] for k in keys if k.startswith("hold_D")), None)
        a2q = next((st[k] for k in keys if k.endswith("_to_q") and not k.startswith("clk")), None)
        rec = next((st[k] for k in keys if k.startswith("recovery")), None)
        rem = next((st[k] for k in keys if k.startswith("removal")), None)
        ctq = st.get("clk_to_q", st.get("clk_to_q_neg"))
        f = lambda v: "-" if v is None else f"{v:.0f}"
        P(f"| {n} | {c.area:.4f} | {c.area/nand:.3f} | {f(ctq)} | {f(setup)} | {f(hold)} | {f(a2q)} | {f(rec)} | {f(rem)} | {note} |")
        seq[n] = dict(area=c.area, ge=round(c.area / nand, 4), timing_ps={k: round(v, 1) for k, v in st.items()})
    facts["sequential"] = seq
    # clock-period proxy examples
    d = seq["dfxtp_1"]["timing_ps"]
    P("\nT_clk,min = clk->Q + T_comb + setup (+ nothing else: ideal clock, zero skew). For dfxtp_1 the register overhead is "
      f"clk->Q {d['clk_to_q']:.0f} ps + setup {d['setup_D']:.0f} ps = {d['clk_to_q'] + d['setup_D']:.0f} ps; "
      f"dfrtp_1: {seq['dfrtp_1']['timing_ps']['clk_to_q'] + seq['dfrtp_1']['timing_ps']['setup_D']:.0f} ps.")

    # ---------------------------------------------------------------- 4. drive strengths
    P("\n### Drive-strength variants: area and delay at a fixed condition (input slew 50 ps, load 10 fF; worst arc; ps)\n")
    P("| family | size | um^2 | GE | input cap fF (pin A or A1) | delay rise | delay fall | delay at load 40 fF (rise) |\n|---|--:|--:|--:|--:|--:|--:|--:|")
    drive = {}
    for fam in ["inv", "buf", "nand2", "nor2", "and2", "or2", "xor2", "xnor2", "mux2", "a21oi", "o21ai", "nand3"]:
        for sz in ("0", "1", "2", "4", "8", "16"):
            n = f"{fam}_{sz}"
            if not lib.has(LIBP(n)):
                continue
            c = lib.cell(LIBP(n))
            r, f_ = delay_ps(c, 0.05, 0.010)
            r40, _ = delay_ps(c, 0.05, 0.040)
            pin = next(iter(c.pin_cap))
            P(f"| {fam} | {sz} | {c.area:.4f} | {c.area/nand:.2f} | {c.pin_cap[pin]*1000:.2f} | {r:.0f} | {f_:.0f} | {r40:.0f} |")
            drive[n] = dict(area=c.area, cin_ff=round(c.pin_cap[pin] * 1000, 3), d_rise_ps=round(r, 1), d_fall_ps=round(f_, 1), d40_ps=round(r40, 1))
    facts["drive"] = drive

    # ---------------------------------------------------------------- 5. units / power sign convention
    P("\n### Units and the sign convention of the power tables\n")
    P("Liberty header: time_unit " + str(lib.attrs["time_unit"]) + ", capacitive_load_unit " + " ".join(lib.attrs["capacitive_load_unit"]) +
      ", voltage_unit " + str(lib.attrs["voltage_unit"]) + ", current_unit " + str(lib.attrs["current_unit"]) +
      ", leakage_power_unit " + str(lib.attrs["leakage_power_unit"]) + " -> internal_power tables are V x mA x ns = pJ; pin capacitances are pF (Nangate45: fF).\n")
    c = lib.cell(LIBP("nand2_1"))
    pw = c.power["Y"]
    P("nand2_1 output Y, mean over its power tables, at input slew 50 ps; ½CV² with V = 1.8 V in the last column (fJ):\n")
    P("| load fF | rise_power fJ | fall_power fJ | rise + fall fJ | ½CV² fJ |\n|--:|--:|--:|--:|--:|")
    sc = []
    for load in (0.0005, 0.002, 0.005, 0.010, 0.040, 0.1666):
        er = sum(t.at(0.05, load) for t in pw["rise_power"]) / len(pw["rise_power"]) * 1000
        ef = sum(t.at(0.05, load) for t in pw["fall_power"]) / len(pw["fall_power"]) * 1000
        P(f"| {load*1000:.1f} | {er:.2f} | {ef:.2f} | {er+ef:.2f} | {0.5*load*1.8*1.8*1000:.2f} |")
        sc.append((load, er, ef))
    P("\nrise_power is about +½CV² above a load-independent part and fall_power about -½CV² below it: the tables are SIGNED and already contain the load's "
      "charge/discharge. A rise followed by a fall (every net alternates) leaves 2 x the cell's own internal energy; a table value alone is not a per-toggle energy.")
    facts["power_sign"] = [dict(load_pf=a, rise_fj=b, fall_fj=c_) for a, b, c_ in sc]

    # ---------------------------------------------------------------- 6. policy census
    cnt = collections.Counter(S.cell_class(n)[0] for n in lib._cells)
    P("\n### Cell policy census (428 cell groups)\n")
    P("| class | cells | allowed in a combinational scored netlist | reason |\n|---|--:|---|---|")
    reasons = {}
    for pat, cls, why in S.POLICY:
        reasons.setdefault(cls, why)
    reasons["logic"] = "ordinary combinational cells, every drive strength (including _0, buffers, inverters, constant-free)"
    for cls in ["logic", "sequential", "low-power-flow", "clock", "tristate", "physical-only", "multi-output", "delay", "tie"]:
        P(f"| {cls} | {cnt[cls]} | {'yes' if cls == 'logic' else 'no'} | {reasons[cls]} |")
    facts["policy_census"] = dict(cnt)
    os.makedirs(SD.DATA, exist_ok=True)
    json.dump(facts, open(os.path.join(SD.DATA, "facts.json"), "w"), indent=1, sort_keys=True)
    open(os.path.join(SD.DATA, "facts.md"), "w").write("\n".join(md) + "\n")
    print("\n".join(md))


if __name__ == "__main__":
    main()
