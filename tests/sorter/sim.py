#!/usr/bin/env python3
"""Validation of the `sorter` reference (and of mutants of it) by simulation, against C8.

    python3 sim.py [--design FILE] [--seeds K] [--no-mutants]

Icarus Verilog (4-state, so every register starts x) runs tb.sv on oracle.py's transactions at the
probe points; tb.sv observes Idle and drives the C8 protocol, with one extra transaction that is
aborted by a mid-stream reset. The claim is then checked HERE, from the printed trace alone, as an
executable reading of StreamTask.Rely/Guar (SvGolf/TaskSeq.lean), per reset release c1 and horizon h:
out_valid known at every cycle; 0 before the first start; for every start s with s + lat < h, the
cycles with out_valid = 1 from s to the next start are exactly N, at most lat after s, with known
out_data whose values are oracle.good. A start that is not Idle (a mutant that never finishes)
ends the horizon. Mutants are text substitutions of the reference (MUTANTS), each expected to FAIL
or, for the equivalent ones, to PASS. Exit status 0 iff every expectation holds.
"""
import argparse, importlib.util, os, re, subprocess, sys, tempfile

sys.dont_write_bytecode = True   # no __pycache__ in tasks/sorter/ (a player-facing directory)
HERE = os.path.dirname(os.path.abspath(__file__))
TASK = os.path.join(HERE, "..", "..", "tasks", "sorter")
_spec = importlib.util.spec_from_file_location("sorter_oracle", os.path.join(TASK, "oracle.py"))
oracle = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(oracle)
POINTS = oracle.PROBE_POINTS
LAT = lambda n, w: 2 * n                                     # the reference's claimed latency

# (name, old, new, expected verdict at the probe points). `old` must occur in the reference.
MUTANTS = [
    ("loop bound off by one (cell N-2 never written)", "k < N-1; k++", "k < N-2; k++", "FAIL"),
    ("missing else: both cell branches fire, the last NBA wins",
     "else if (in_data > data[k*W +: W])", "if (in_data > data[k*W +: W])", "FAIL"),
    ("neighbour push compares the cell's own value", "if (in_data > data[(k+1)*W +: W])",
     "if (in_data > data[k*W +: W])", "FAIL"),
    ("early out_valid (token read one cell up)", "out_valid <= tok[0];",
     "out_valid <= tok[N > 1 ? 1 : 0];", "FAIL"),
    ("reset does not clear cells 0..N-2", "        data[k*W +: W] <= '0;\n", "", "FAIL"),
    ("top cell not cleared by the drain (stale max)", "end else\n      data[(N-1)*W +: W] <= '0;",
     "end", "FAIL"),
    ("signed instead of unsigned order", re.compile(r"in_data > (data\[[^\]]*\])"),
     r"$signed(in_data) > $signed(\1)", "FAIL"),
    ("EQUIVALENT: >= for > everywhere (ties)", "in_data > ", "in_data >= ", "PASS"),
    ("EQUIVALENT: >= in the neighbour push only", "if (in_data > data[(k+1)*W +: W])",
     "if (in_data >= data[(k+1)*W +: W])", "PASS"),
]


def mutate(text, old, new):
    if isinstance(old, re.Pattern):
        out, k = old.subn(new, text)
    else:
        k, out = text.count(old), text.replace(old, new)
    assert k >= 1, f"mutant pattern {old!r} not in the reference"
    return out


def stimulus(n, w, seed, abort=True):
    ts = oracle.txns({"N": n, "W": w}, seed)
    lines = [f"{t['gap']} -1 {len(t['free'])} " + " ".join(map(str, t["xs"] + t["free"])) for t in ts]
    if abort:   # a transaction cut by a reset after N//2 inputs, then the stream goes on
        t = ts[5]
        lines.insert(4, f"1 {n // 2} {len(t['free'])} " + " ".join(map(str, t["xs"][::-1] + t["free"])))
    return lines


def simulate(design, n, w, lat, lines, work):
    with open(os.path.join(work, "design.sv"), "w") as fh:
        fh.write(design)
    with open(os.path.join(work, "stim.txt"), "w") as fh:
        fh.write("\n".join(lines) + "\n")
    cmd = ["iverilog", "-g2012", "-s", "tb", "-P", f"tb.N={n}", "-P", f"tb.W={w}", "-P", f"tb.LAT={lat}",
           "-o", "sim.vvp", os.path.join(HERE, "tb.sv"), "design.sv"]
    p = subprocess.run(cmd, cwd=work, capture_output=True, text=True)
    if p.returncode:
        return None, "compile: " + (p.stderr or p.stdout).strip().splitlines()[0]
    p = subprocess.run(["vvp", "-n", "sim.vvp"], cwd=work, capture_output=True, text=True, timeout=600)
    rows = [l.split()[1:] for l in p.stdout.splitlines() if l.startswith("E ")]
    return [(int(c), r, s, v, d, ov, od) for c, r, s, v, d, ov, od in rows], None


def check(rows, n, w, lat):
    """None or the first violation; stats in a dict."""
    st = {"claimed": 0, "first": set(), "last": set(), "segments": 0}
    for c1 in [c for c in range(1, len(rows)) if rows[c][1] == "0" and rows[c - 1][1] == "1"]:
        h = next((c for c in range(c1, len(rows)) if rows[c][1] != "0"), len(rows))
        st["segments"] += 1
        starts = [c for c in range(c1, h) if rows[c][2] == "1"]
        valid = lambda a, b: [c for c in range(a, b) if rows[c][5] == "1"]
        for i, s2 in enumerate(starts):            # Rely: a start only when Idle; else the horizon ends
            if any(len(valid(s, s2)) < n for s in starts[:i]):
                h, starts = s2, starts[:i]
                break
        for c in range(c1, h):
            if rows[c][5] not in ("0", "1"):
                return f"out_valid = {rows[c][5]} at cycle {c}", st
            want_iv = "1" if any(s < c <= s + n for s in starts) else "0"
            if rows[c][3] != want_iv:
                return f"stimulus breaks the rely: in_valid at {c}", st
        if valid(c1, starts[0] if starts else h):
            return f"out_valid = 1 before the first start (cycle {valid(c1, h)[0]})", st
        for i, s in enumerate(starts):
            if s + lat >= h:
                continue
            e = starts[i + 1] if i + 1 < len(starts) else h
            xs = [int(rows[s + 1 + j][4], 16) for j in range(n)]
            vs = valid(s, e)
            if any(not re.fullmatch(r"[0-9a-f]+", rows[c][6]) for c in vs):
                return f"out_data unknown while out_valid = 1 (start {s})", st
            out = [int(rows[c][6], 16) for c in vs]
            bad = oracle.mismatch({"N": n, "W": w}, {"xs": xs, "tag": f"start {s}"}, {"out": out})
            if bad:
                return bad, st
            if vs[-1] - s > lat:
                return f"output at {vs[-1] - s} cycles after start {s}, lat = {lat}", st
            st["claimed"] += 1
            st["first"].add(vs[0] - s)
            st["last"].add(vs[-1] - s)
    return None, st


def run(design, n, w, lat, seeds, work):
    total, firsts, lasts = 0, set(), set()
    for seed in seeds:
        rows, err = simulate(design, n, w, lat, stimulus(n, w, seed), work)
        if err:
            return err, None
        err, st = check(rows, n, w, lat)
        if err:
            return f"N={n},W={w} seed {seed}: {err}", None
        total, firsts, lasts = total + st["claimed"], firsts | st["first"], lasts | st["last"]
    return None, (total, firsts, lasts)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--design", default=os.path.join(TASK, "reference", "sorter_ins.sv"))
    ap.add_argument("--seeds", type=int, default=3)
    ap.add_argument("--no-mutants", action="store_true")
    a = ap.parse_args()
    ref = open(a.design).read()
    ok = True
    with tempfile.TemporaryDirectory(dir=os.environ.get("SORTER_SCRATCH")) as work:
        print(f"{'point':10} {'txns':>5} {'first':>7} {'last':>7}  lat  verdict")
        for n, w in POINTS:
            err, res = run(ref, n, w, LAT(n, w), range(a.seeds), work)
            if err:
                ok = False
                print(f"N={n},W={w}  FAIL {err}")
                continue
            t, f, l = res
            fmt = lambda s: f"{min(s)}..{max(s)}" if len(s) > 1 else str(min(s))
            print(f"N={n},W={w:<4} {t:>5} {fmt(f):>7} {fmt(l):>7}  {LAT(n, w):>3}  PASS")
        if a.no_mutants:
            return 0 if ok else 1
        print("\nmutants (each at every probe point until the first failure):")
        cases = [(m, mutate(ref, old, new), None, want) for m, old, new, want in MUTANTS]
        cases.append(("latency claimed as 2N-1", ref, lambda n, w: 2 * n - 1, "FAIL"))
        for name, text, lat, want in cases:
            err = None
            for n, w in POINTS:
                err, _ = run(text, n, w, (lat or LAT)(n, w), range(a.seeds), work)
                if err:
                    break
            got = "FAIL" if err else "PASS"
            ok &= got == want
            print(f"  {'ok ' if got == want else 'BAD'} {got}  {name}" + (f"\n        {err}" if err else ""))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
