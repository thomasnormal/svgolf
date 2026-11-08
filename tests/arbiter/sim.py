#!/usr/bin/env python3
"""Simulation check of the task `arbiter` (tasks/arbiter/Spec.lean) on its goalpost, designs and attacks.

    python3 sim.py [--out DIR] [--cycles C] [--axis DIR] [--ot FILE]

Icarus Verilog runs tb.sv, an executable reading of the statement per snapshot (G0, G1..G4)
plus the silicon view MO that `MooreOut` guarantees (gnt does not move between a snapshot and the
next edge), on every design at N = 1, 2, 3, 4, 5, 8 and the four stimulus modes (random requests,
hold-until-granted, all requesting, and since 2026-11-07 sparse: one client alone or nobody, frequent
resets). Since 2026-11-07 each run starts the design from a 0/1 POWER-UP state, as the statement's runs
do (txtask-v2 rule 2): Yosys reads the design at N (`proc`) and gives every flip-flop and every undriven
variable a value (`setundef -undriven -init`: all zeros in mode 0, a random state seeded by (N, mode) in
the others; then `opt_clean`, which moves an init that `setundef` put on a copy of a flip-flop's output,
`base = ptr`, onto the flip-flop's own variable, where `write_verilog` keeps it), and Icarus simulates
that copy (tb.sv `POWERUP`). The copy is read back by Yosys before it runs, and a flip-flop or latch bit
without a 0/1 power-up value, or a memory, is an ERROR, never a run from x (`powerup`, 2026-11-07, the
review's F1: a lost init made a wrong design's all-x grant fire no check). The check that gnt is KNOWN
(KN) is gone with the x start it tested (rule 3, XSafe, makes every value known in the statement), which
wrongly killed the correct mutant m067 (its mask is never reset: x for ever in Icarus); in its place XK,
a self-check of the harness, counts an unknown gnt after a 0/1 power-up, which a correct power-up of an
x-safe design cannot give. The third-party `--axis` and `--ot` sources still run from Icarus's x start
(XK off). A design PASSES iff no check fires anywhere. Each design's
expected verdict is EXPECT below (the attack list of tasks/arbiter/README.md); exit status 0 iff
every expectation holds. The designs: the goalpost tasks/arbiter/reference/rr_mask.sv, designs/
(rotate.sv, a different fair policy; arbiter_ot.sv, the adapted OpenTitan tree behind an output
register, the real-world reference candidate), attacks/ and selftest/ (the harness's own regression, a
wrong design whose power-up the old harness lost). `--axis DIR` adds verilog-axis
`arbiter.v` + `priority_encoder.v`, `--ot FILE` the probe's adapted OpenTitan `prim_arbiter_tree.sv`
(registered by tb.sv's own wrapper, and raw): third-party sources, read by the simulator only.
`--points` and `--cycles` shorten the run (tests/run.py's quick plan).
"""
import argparse, glob, json, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
POINTS = [1, 2, 3, 4, 5, 8]
MODES = [0, 1, 2, 3]
CHECKS = ["G0", "G1", "G2", "G3", "G4", "MO", "XK"]
YOSYS = os.environ.get("SVGOLF_YOSYS") or "yosys"

# design -> (expected verdict, the checks expected to fire at some point[, the checks that must not fire])
EXPECT = {
    "../../tasks/arbiter/reference/rr_mask.sv": ("PASS", set()),
    "designs/rotate.sv": ("PASS", set()),
    "designs/arbiter_ot.sv": ("PASS", set()),
    "attacks/a01_never.sv": ("FAIL", {"G3", "G4"}),
    "attacks/a02_everyone.sv": ("FAIL", {"G1"}),
    "attacks/a03_zero.sv": ("FAIL", {"G2"}),
    "attacks/a04_fixed.sv": ("FAIL", {"G4"}),
    "attacks/a05_ring.sv": ("FAIL", {"G2"}),
    "attacks/a06_tdma.sv": ("FAIL", {"G3"}),
    "attacks/a07_late.sv": ("FAIL", {"G2", "G3"}),
    "attacks/a08_sticky.sv": ("FAIL", {"G4"}),
    "attacks/a09_rotate_pow2.sv": ("FAIL", {"G4"}),
    "attacks/a10_mealy_last.sv": ("FAIL", {"MO"}),
    "attacks/a11_noreset.sv": ("FAIL", {"G0"}),
    "attacks/a12_stale_mask.sv": ("FAIL", {"G4"}),
    "attacks/a13_async.sv": ("FAIL", {"MO"}),
    "attacks/a14_mealy_rr.sv": ("FAIL", {"MO"}),
    "attacks/a15_half_rate.sv": ("FAIL", {"G3"}),
    # review 11/04: two WRONG designs that 4-state RTL simulation from Icarus's x start could not see; the
    # statement rejects both (README "Review"). A16 (x-optimism behind a never-reset `u`) fails G4 here since
    # the runs start from 0/1 power-up states (2026-11-07: from u = 0 it is fixed priority, the statement's
    # refutation); A17 (fixed priority after 4095 cycles) still passes: a reset every ~256 entries (16 in
    # mode 3) never lets it reach its bomb; the statement rejects it by G4 on a longer segment
    "attacks/a16_xopt.sv": ("FAIL", {"G4"}),
    "attacks/a17_timebomb.sv": ("PASS", set()),
    # the harness's own regression (review F1, 2026-11-07): a never-reset pointer copied to another variable
    # (`base = ptr`), wrong from a power-up ptr >= N (it grants nothing); Yosys put the power-up value on the
    # copy and Icarus ran ptr from x, an all-x grant that fired no check. It must reach a 0/1 power-up (the
    # self-check XK stays 0) and fail on its clause.
    "selftest/alias_ptr.sv": ("FAIL", {"G3"}, {"XK"}),
    "axis": ("PASS", set()),
    "ot_reg": ("PASS", set()),
    "ot_raw": ("FAIL", {"MO"}),
}
RES = re.compile(r"RESULT N=(\d+) MODE=(\d+) cycles=(\d+) grants=(\d+) " +
                 " ".join(f"{c}=(\\d+)" for c in CHECKS) + r" maxmiss=(\d+)")


def uninitialized(net):
    """The state the written copy leaves without a 0/1 power-up value, from Yosys's JSON of the copy read back
    (`proc`): the names of the flip-flop and latch bits (every cell with a `Q`) that no `init` attribute gives a
    0 or 1, and every memory. Empty iff every run of the copy starts from a 0/1 state."""
    mods = [m for m in net["modules"].values() if not m.get("attributes", {}).get("blackbox")]
    bad = []
    for m in mods:
        known, name = set(), {}
        for nm, w in sorted(m["netnames"].items(), key=lambda kv: kv[0].startswith(("$", "_"))):
            for i, b in enumerate(w["bits"]):
                if isinstance(b, int):
                    name.setdefault(b, f"{nm}[{i}]")      # a source name first, then Yosys's own
            init = w.get("attributes", {}).get("init")
            if isinstance(init, str):
                init = init.rjust(len(w["bits"]), "x")        # MSB first; Yosys pads a short constant with x
                known |= {b for i, b in enumerate(w["bits"]) if isinstance(b, int) and init[-1 - i] in "01"}
        for cn, c in m["cells"].items():
            if c["type"].startswith("$mem"):
                bad.append(f"memory {cn}")
            bad += [name.get(b, f"bit {b}") for b in c["connections"].get("Q", [])
                    if isinstance(b, int) and b not in known]
    return sorted(set(bad))


def powerup(srcs, n, mode, work):
    """The design `arbiter` at N = n from a 0/1 power-up state (above): Yosys's reading of `srcs` (`proc`), every
    flip-flop and undriven variable set (`setundef -undriven -init`: -zero in mode 0, -random (n, mode) in the
    others), `opt_clean` (an init on a copy of a flip-flop's output moves to the flip-flop's variable), written
    for Icarus, then read back: a state bit of the copy without a 0/1 init is an error (`uninitialized`).
    Returns (path, None) or (None, the error's first lines)."""
    out = os.path.join(work, f"pu_N{n}_m{mode}.v")
    chk = os.path.join(work, f"pu_N{n}_m{mode}.json")
    how = "-zero" if mode == 0 else f"-random {1000 * n + mode}"
    script = (" ".join(f'read_verilog -sv "{s}";' for s in srcs)
              + f" hierarchy -top arbiter -chparam N {n}; proc; setundef -undriven -init {how}; opt_clean;"
              + f' write_verilog -noattr "{out}"; design -reset; read_verilog -sv "{out}"; proc;'
              + f' write_json "{chk}"')
    r = subprocess.run([YOSYS, "-q", "-p", script], capture_output=True, text=True)
    if r.returncode != 0 or not os.path.isfile(out) or not os.path.isfile(chk):
        return None, (r.stdout + r.stderr).strip().splitlines()[-3:]
    with open(chk) as fh:
        bad = uninitialized(json.load(fh))
    if bad:
        return None, [f"power-up: the copy at N={n} (mode {mode}) leaves {len(bad)} state bit(s) without a 0/1 "
                      f"value, so Icarus would run them from x: {', '.join(bad[:8])}"]
    return out, None


def run(srcs, defines, n, mode, cycles, work):
    exe = os.path.join(work, "a.vvp")
    if not defines:                  # a design of this task: from a 0/1 power-up state (tb.sv POWERUP)
        pu, err = powerup(srcs, n, mode, work)
        if pu is None:
            return None, err
        srcs, defines = [pu], ["POWERUP"]
    cmd = ["iverilog", "-g2012", "-o", exe, f"-Ptb.N={n}", f"-Ptb.MODE={mode}", f"-Ptb.CYCLES={cycles}"]
    cmd += [f"-D{d}" for d in defines] + [os.path.join(HERE, "tb.sv")] + srcs
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        return None, r.stderr.strip().splitlines()[:3]
    r = subprocess.run(["vvp", "-n", exe], capture_output=True, text=True, cwd=work)
    m = RES.search(r.stdout)
    if not m:
        return None, (r.stdout + r.stderr).strip().splitlines()[-3:]
    g = list(map(int, m.groups()))
    return {"grants": g[3], **{c: g[4 + i] for i, c in enumerate(CHECKS)}, "maxmiss": g[-1]}, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cycles", type=int, default=20000)
    ap.add_argument("--axis", help="directory with verilog-axis arbiter.v and priority_encoder.v")
    ap.add_argument("--ot", help="the adapted OpenTitan prim_arbiter_tree.sv")
    ap.add_argument("--out", help="working directory (default: a fresh temporary one)")
    ap.add_argument("--points", help=f"comma-separated N (default {','.join(map(str, POINTS))})")
    a = ap.parse_args()
    points = [int(x) for x in a.points.split(",")] if a.points else POINTS
    work = a.out or tempfile.mkdtemp(prefix="arbsim-")
    os.makedirs(work, exist_ok=True)
    jobs = [(k, [os.path.normpath(os.path.join(HERE, k))], [])
            for k in ["../../tasks/arbiter/reference/rr_mask.sv"] + sorted(glob.glob("designs/*.sv", root_dir=HERE))
            + sorted(glob.glob("attacks/*.sv", root_dir=HERE)) + sorted(glob.glob("selftest/*.sv", root_dir=HERE))]
    if a.axis:
        jobs.append(("axis", [os.path.join(a.axis, "arbiter.v"), os.path.join(a.axis, "priority_encoder.v")], ["AXIS"]))
    if a.ot:
        jobs += [("ot_reg", [a.ot], ["OTREG"]), ("ot_raw", [a.ot], ["OTRAW"])]
    ok = True
    for name, srcs, defs in jobs:
        fired, worst, err, per_n = set(), 0, None, {}
        for n in points:
            fn = set()
            for mode in MODES:
                res, e = run(srcs, defs, n, mode, a.cycles, work)
                if res is None:
                    err = e
                    break
                fn |= {c for c in CHECKS if res[c] > 0}
                worst = max(worst, res["maxmiss"])
            if err:
                break
            per_n[n] = fn
            fired |= fn
        verdict = "ERROR" if err else ("PASS" if not fired else "FAIL")
        exp = EXPECT.get(name)
        good = exp is not None and verdict == exp[0] and exp[1] <= fired and not (exp[2:] and exp[2] & fired)
        ok &= good
        where = " ".join(f"N{n}:{'+'.join(sorted(f)) or '-'}" for n, f in per_n.items())
        print(f"{'ok ' if good else 'BAD'} {name:28s} {verdict:5s} fired={'+'.join(sorted(fired)) or '-':12s}"
              f" max_wait={worst:<3d} {where}" + (f"  {err}" if err else ""))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
