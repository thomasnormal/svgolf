#!/usr/bin/env python3.12
"""svGolf post-synthesis simulation check: ls-sv and the SCORED netlist agree.

The proof is about ls-sv's reading of the design (the envelope the checker's
`extract` stage wrote, `design.sem` of `load_design_sv2`); the score is about
the gate netlist the pinned Yosys + ABC flow produced from the same canonical
text. The source gate makes the two tools read one text, but it cannot make
them give that text one meaning: where they differ (4-state `x`/`z` in case
items, `===`, undriven nets, a synthesis don't-care, a Yosys or ls-sv bug),
the proved circuit and the scored circuit are two circuits. This stage
compares them vector by vector at the scoring point and rejects the
submission when they differ anywhere it looks. Its VERDICT does not compare
against the task's function: the proof already ties ls-sv's reading to it. (An
ADVISORY smoke check does, below: "FUNCTIONAL SMOKE CHECK".)

  ls-sv     `svgolf-eval` (`check/SvEval.lean`, built in the `trusted`
            stage): `design.sem` at the point, one fresh one-cycle `run2`
            per vector under `σ_src` and under `σ_rev`;
  netlist   Verilator (`verilator --cc --build`, one C++ model per run) on the
            netlist the scoring run itself wrote (`score/svgolf.ys`'s last
            line, after `stat` and `ltp`) plus Yosys's `simcells.v`, driven by
            a small generated C++ harness that reads ALL the vectors and
            prints one row per vector; first, a fresh Yosys process re-reads
            that netlist and must count exactly the scored gates by type and
            the scored depth (so the file simulated IS the netlist scored);
  RTL       (bug report only) Verilator on the canonical source at the point,
            a third opinion for the first REPORT_MAX failing vectors.

TWO-STATE NETLIST SIMULATION. Verilator has no `x` and no `z`: every signal is
0 or 1, so this stage CANNOT SEE an unknown value inside the netlist. (The
earlier Icarus version printed `x` through it; that is lost, and this says
what stands in its place.) A netlist of Yosys's gate cells (`simcells.v`:
`assign Y = A & B;`, `assign Y = S ? B : A;`, each a total Boolean function)
driven by known inputs can only hold an unknown through an unknown-valued
CONSTANT or an UNDRIVEN net or pin, and both are refused here wherever
something can read them:
  * Yosys's own reader decides (`reread_check` writes its JSON view of the
    re-read netlist, every module; `unknown_bits`): an unknown-valued
    constant bit (`x` or `z`) that a cell input pin (or a pin whose direction
    is not known, or an inout), a flip-flop's D, or an output or inout port
    bit carries is REJECTED, on every vector of a combinational task (what the
    4-state run did by printing `x`; the bug report still shows what a 2-state
    model reads: Verilator gets `--x-assign 0 --x-initial 0` and
    `randReset(0)`, so an unknown it is handed is a fixed 0, never an
    unspecified value) and at once on a clocked one. The message names the
    netlist's wires that hold it and its readers, and the bits in the
    design's own names where a NAMING run (`unknown_names`, made only for
    the refusal, never deciding anything) gives them. A constant that NOTHING
    reads is accepted and listed in the record (`netlist_unread_unknown`):
    Yosys leaves one where it removed an unused register bit (the bits of one
    vector written by separate processes, one of them never read), and
    because Yosys's reader resolves every alias, a bit no cell input and no
    output port carries is in the fan-in of nothing the harness observes, so
    every value Verilator gives it yields the same rows (decided 2026-11-11);
  * where that view could hide one, the rule fails safe (`reread_check`,
    decided 2026-11-12): a net bit with more than one driver of which one is
    an unknown constant is REJECTED wherever it is (Yosys's view keeps only
    one driver of a bit, so it would show a `0` for `assign y = 1'b0; assign
    y = 1'hx;`; the drivers are counted in a second view, `insbuf`'s, in
    which every assign is a buffer cell of its own: `conflicting_drivers`),
    and so is a netlist that defines a box module (`(* blackbox *)`,
    `whitebox`, `lib_whitebox`) or has a cell whose type is neither a gate
    cell of `simcells.v` nor a module the netlist defines (`opaque_parts`):
    the rule cannot look inside either. A netlist the pinned flow writes has
    neither (`write_verilog -noattr -noexpr`: gate instances and assigns of
    single drivers);
  * a combinational loop is refused BIT BY BIT before anything is simulated
    (`comb_loops`, 2026-11-13): in the `insbuf` view every assign is a
    buffer cell, every cell but the flip-flop `$_DFF_P_` leads from each of
    its input pins to each of its output pins, and a cycle of net bits is a
    loop, wherever it is;
  * Verilator's lint runs with `-Wall`, every warning FATAL but the three in
    `NETLIST_WNO`: an undriven net (UNDRIVEN), a gate pin left open
    (PINMISSING, PINCONNECTEMPTY), a doubly driven net (MULTIDRIVEN), a width
    mismatch and an unknown cell all reject. The third waived warning is
    UNOPTFLAT, Verilator's loop warning, which works at the granularity of a
    whole VECTOR: Yosys writes flip-flops it merged as assigns between bits of
    one vector (`assign { q[2], q[0] } = { q[3], q[1] };`), which it calls
    circular although no bit depends on itself. With the bit-level rule
    above refusing every real loop first, what is left of UNOPTFLAT is that
    false one, which Verilator simulates correctly, only more slowly (its
    manual on the warning: "Ignoring this warning will only slow
    simulations; it will simulate correctly"); a model whose logic does not
    settle stops with an error (DIDNOTCONVERGE) and is rejected;
  * the defences upstream stay what they were: the source gate refuses every
    x/z literal source, the `fourstate` stage refuses undriven or conflicting
    nets, loops and out-of-range selects, and ls-sv's side of this stage stays
    4-state, so an `x`/`z` in ls-sv's outputs still rejects.
What the 2-state model cannot give is a witness for an unknown that the
netlist computes on its own from known inputs and driven nets; with Yosys
gate cells there is none to find. A sequential cell (a latch, a flip-flop) is
refused earlier, by the score (README.md, "Scoring").

BUILD AND RUN. The model is built once per run (`verilator --cc` then `make`,
about 1.5 s for the runtime plus the model; no compiler cache), concurrently
with ls-sv's evaluation, from the netlist, `simcells.v` and a generated C++
harness. The harness reads every vector of one file, `eval()`s the model per
vector and prints one row of binary strings per vector, then `END <rows>`; a
nonzero exit, a missing or wrong end marker, a different number of rows than
vectors, or a row of the wrong shape rejects. A failure of the C++ build
itself (not of the lint) is an infrastructure error: the toolchain, not the
design, is broken. About 0.4 microseconds per vector on the 1400-gate
netlists, so the netlist side no longer limits the vector budget: ls-sv's
`run2` does.

VECTORS, all deterministic (fully known 0/1 inputs, duplicates dropped):
  fixed     all-0, all-1, and walking ones and walking zeros on each input
            with the other inputs all-0 and all-1;
  corners   the task's `postsynth.corners` (`{port: [values]}`), their
            cartesian product (a port without values: 0 and all-1);
  harvest   every comparison cell (`$eq $ne $eqx $nex $lt $le $gt $ge`) of
            Yosys's coarse design (`proc; flatten; opt -purge`) with a
            constant operand gives a partial input assignment from the
            constant's 0/1 bits (x/z bits stay free): the exact bits when the
            other operand is input-port bits, else the constant on every
            input wide enough; each assignment, and each
            compatible pair (up to `harvest_pairs`), with the free bits
            all-0, all-1 and random twice: a disagreement confined to a
            region selected by a constant comparison
            (`a[7:0] == 8'hEF && b == 16'h1234`) is hit although random
            vectors would hit it with probability 2^-24;
  random    `postsynth.random` vectors from a PRNG seeded with
            sha256(salt, task, point, canonical text); the salt is
            $SVGOLF_POSTSYNTH_SALT (default empty: anyone can reproduce a
            run; a competition sets a secret salt so that a player cannot
            predict the vectors). The seed is recorded.

TWO MODES (decided 2026-10-30): the check runs LIGHT (the default) or FULL.
  full   everything above, exactly: the task's whole budget (the fixed
         vectors, the task corners, every harvested constant and compatible
         pair, `postsynth.random` random vectors). What a competition and
         the leaderboard's `add` / `verify` run, and what `tests/run.py`
         pins; it is the only mode a record may be official in.
  light  a deterministic SUBSET of the full vector set, for local feedback
         (`check.py`'s default): all-0 and all-1, plus at most Q = (L - 2) / 4
         vectors from each of four classes, L = `postsynth.light_vectors`
         (default 256): the walking ones/zeros (evenly spaced), the task
         corners (evenly spaced), the harvested constants (the 0 and 1 fills
         of each constant's assignment, then of the pairs), and the seeded
         random vectors (the FIRST of the full stream, and everything the
         other classes leave unused). Everything else is the same code and the
         same verdicts: the netlist read-back, the unknown-constant rule,
         Verilator's lint, the x/z, schedule and port checks, the bug report
         with its Verilator-RTL third opinion (built only to illustrate a
         rejection, in either mode). Because the light set is a subset of the
         full one with the same seed, a light rejection is a full rejection;
         what light can miss is a difference that only the dropped vectors
         reach. The mode ($SVGOLF_POSTSYNTH or `check.py --postsynth`, the
         flag wins, default light), the vector counts of both modes
         (`vectors`, `full_vectors`) and the seed are in the record.

VERDICT (fail closed): the submission is REJECTED when an ls-sv run does not
complete (timeout, unsupported, a bad trace), when any output digit is `x` or
`z` on either side, when `σ_src` and `σ_rev` disagree, when the port sets
(direction, name, width) differ, when the netlist does not re-read as the
scored one, when something in the netlist reads an unknown-valued constant, when Verilator
cannot lint, compile or run it cleanly (any lint warning outside the waived
list, a compile error, a nonzero exit, a harness that prints a different number
of rows than there are vectors or no end marker), when the ls-sv evaluation
overruns `postsynth.time_limit_s`, or when any output differs between ls-sv
and the netlist. A missing tool (Verilator, a C++ compiler, `make`, Yosys,
`svgolf-eval` not built) is an infrastructure error. A rejection carries a
BUG REPORT: per failing vector the inputs, ls-sv's outputs, the netlist's,
Verilator-on-RTL's, and which of the three agree.

FUNCTIONAL SMOKE CHECK (ADVISORY; never a verdict). A task may name a Python
ORACLE in its task.json (`"oracle": "oracle.py"`, a file of the task
directory defining `oracle(params, inputs) -> outputs`: `params` the point
this run uses, `inputs` port name -> int, the result output port name -> int
already masked to the output width). The values ls-sv already computed for the
vectors above are compared with the oracle's: no new simulator run. The
result is the record's `functional` object

    {"checked": K, "mismatches": M, "examples": [up to 3 of
     {"point", "inputs", "expected", "got"}]}      (values as hex strings)

plus `"unchecked": U` and `"note": why` when some vector could not be compared
(ls-sv gave no known value for it, or the oracle raised, returned the wrong
ports or an out-of-range value: those are never counted as mismatches), and
check.py adds ONE `warnings` line when M > 0. It changes no verdict, no field
and no stage: a design that computes something else than the task's function
cannot be proved, and this tells a contestant so before the Lean error does.
The oracles are NOT part of the trusted statement (SvGolf/Task.lean and
tasks/*/Spec.lean are); a task without an oracle has no `functional` key.

It is sampling, not proof: a disagreement confined to a rare input region
not selected by a constant comparison can pass (README.md, "Rules").

Standalone (research, baselines; the checker calls `run` itself):

    python3.12 check/postsynth.py --task tasks/<name> DESIGN.sv [--point N=32]
        [--mode light|full] [--random K] [--third-all] [--keep DIR] [--json OUT]

gates the design, extracts it (`check/envelope.py`, with the point as the only
probe point), scores it (`score/score.py`, keeping the netlist) and runs the
check. Exit status 0 =
agree, 1 = rejected (or the design is refused before the check), 2 =
infrastructure error.
"""

import argparse
import concurrent.futures
import hashlib
import itertools
import json
import os
import random
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(SVGOLF, "score"))
sys.path.insert(0, HERE)
import envelope  # noqa: E402
import sandbox  # noqa: E402  (the scrubbed environment of every child process)
import score  # noqa: E402

SVEVAL = os.environ.get("SVGOLF_SVEVAL") or os.path.join(SVGOLF, ".lake", "build", "bin",
                                                         "svgolf-eval")
# Defaults of a task's `postsynth` block (README.md, the task.json table).
DEFAULTS = {"random": 1000, "harvest_pairs": 2000, "fuel": 100000, "time_limit_s": 900,
            "corners": {}, "light_vectors": 256}
# The two modes (module docstring, "TWO MODES"). `light` is the default of
# check.py and of this file's own command line; $SVGOLF_POSTSYNTH overrides it
# and an explicit argument (check.py --postsynth, --mode here) overrides both.
MODES = ("light", "full")
DEFAULT_MODE = "light"
MODE_ENV = "SVGOLF_POSTSYNTH"
# The clocked kinds' block (`run_clocked`): `points` (None: the scoring point; check.py synthesizes
# the others), per point `seeds` runs, each `reset_cycles` reset entries, `txns` generator items
# and `tail` idle entries after the last transaction. The reactive kind (`react-family`) has no
# transactions: per seed `segments` segments of oracle.py `segments` (a reset entry, then entries
# with the reset deasserted), the last one `long` entries long (a long reset-free run: "THE
# REACTIVE CHECK", below).
CLOCKED_KINDS = ("seq-family", "tx-family", "stream-family", "react-family")
LATENCY_KINDS = ("tx-family", "stream-family")
CLOCKED_DEFAULTS = {"points": None, "seeds": 8, "reset_cycles": 1, "txns": 24, "tail": 3,
                    "fuel": 100000, "time_limit_s": 900}
REACT_DEFAULTS = {"points": None, "seeds": 8, "reset_cycles": 1, "segments": 24, "long": 70000,
                  "fuel": 100000, "time_limit_s": 900}
REPORT_MAX = 20      # failing vectors in the bug report (and simulated as RTL)
CMP_CELLS = {"$eq", "$ne", "$eqx", "$nex", "$lt", "$le", "$gt", "$ge"}


class Reject(Exception):
    def __init__(self, msg, **info):
        super().__init__(msg)
        self.msg, self.info = msg, info


class InfraError(Exception):
    pass


def resolve_mode(explicit=None, environ=None):
    """The post-synthesis mode of a run: `explicit` (a flag) if given, else
    $SVGOLF_POSTSYNTH (empty counts as unset), else `light`. Anything but
    "light" or "full" is an error, never a silent default: a typo in the
    variable a competition sets must not turn into the light check."""
    env = os.environ if environ is None else environ
    if explicit is not None:
        src, val = "the postsynth mode argument", explicit
    elif env.get(MODE_ENV, "") != "":
        src, val = f"${MODE_ENV}", env[MODE_ENV]
    else:
        return DEFAULT_MODE
    if val not in MODES:
        raise InfraError(f"{src} is {val!r}, not one of {list(MODES)}")
    return val


def sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def config(task):
    base = (REACT_DEFAULTS if task.get("kind") == "react-family" else
            CLOCKED_DEFAULTS if task.get("kind") in CLOCKED_KINDS else DEFAULTS)
    cfg = dict(base)
    cfg.update({k: v for k, v in (task.get("postsynth") or {}).items() if not k.startswith("_")})
    unknown = sorted(set(cfg) - set(base))
    if unknown:
        raise InfraError(f"task.json `postsynth` has unknown keys {unknown}")
    if base is REACT_DEFAULTS:
        bad = [k for k in ("seeds", "reset_cycles", "segments", "long")
               if isinstance(cfg[k], bool) or not isinstance(cfg[k], int) or cfg[k] < 1]
        if bad or not isinstance(cfg["points"], (list, type(None))):
            raise InfraError(f"task.json `postsynth`: {bad or ['points']} out of range")
        return cfg
    if base is CLOCKED_DEFAULTS:
        bad = [k for k in ("seeds", "reset_cycles", "txns", "tail")
               if isinstance(cfg[k], bool) or not isinstance(cfg[k], int) or cfg[k] < (k != "tail")]
        if bad or not isinstance(cfg["points"], (list, type(None))):
            raise InfraError(f"task.json `postsynth`: {bad or ['points']} out of range")
        return cfg
    lv = cfg["light_vectors"]
    if isinstance(lv, bool) or not isinstance(lv, int) or lv < 6:
        raise InfraError(f"task.json `postsynth.light_vectors` must be an integer of at least 6, "
                         f"got {lv!r}")
    return cfg


def tool(name):
    p = shutil.which(name)
    if not p:
        raise InfraError(f"`{name}` is not on PATH (the postsynth stage needs Verilator 5, a C++ "
                         "compiler, make and Yosys)")
    return p


def verilator_info():
    """(verilator path, version line, VERILATOR_ROOT). Verilator 5 or newer is
    required (the harness uses the 5.x model API); the version is recorded."""
    exe = tool("verilator")
    try:
        ver = subprocess.run([exe, "--version"], capture_output=True, text=True, check=True,
                             timeout=60, env=sandbox.scrubbed_env()).stdout.strip()
        root = subprocess.run([exe, "--getenv", "VERILATOR_ROOT"], capture_output=True, text=True,
                              check=True, timeout=60, env=sandbox.scrubbed_env()).stdout.strip()
    except subprocess.CalledProcessError as e:
        said = " ".join((e.stderr or e.stdout or "").split())[-500:]
        raise InfraError(f"`verilator` failed (exit {e.returncode}): {said or 'it printed nothing'} (the tools run with "
                         "an allowlisted environment: README.md, \"Sandbox\")")
    except (subprocess.SubprocessError, OSError) as e:
        raise InfraError(f"`verilator --version` failed: {e}")
    m = re.match(r"Verilator (\d+)\.", ver)
    if not m or int(m.group(1)) < 5:
        raise InfraError(f"Verilator 5 or newer is required, found {ver!r}")
    if not root or not os.path.isdir(root):
        raise InfraError(f"Verilator's VERILATOR_ROOT {root!r} is not a directory")
    return exe, ver, root


def cxx_path():
    """The C++ compiler Verilator's makefile will use (`c++` unless $CXX). A missing one is an infrastructure error
    that says where the name came from: $CXX, when it is set, names it."""
    name = os.environ.get("CXX") or "c++"
    try:
        return tool(name)
    except InfraError as e:
        if not os.environ.get("CXX"):
            raise
        raise InfraError(f"{e}; `{name}` is the value of $CXX: set CXX to a compiler on PATH, or unset it to use "
                         "`c++` (README.md, \"Checking\")")


def simcells():
    try:
        dat = subprocess.run([tool("yosys-config"), "--datdir"], capture_output=True, text=True,
                             check=True, env=sandbox.scrubbed_env()).stdout.strip()
    except subprocess.CalledProcessError as e:
        raise InfraError(f"`yosys-config --datdir` failed: {e}")
    path = os.path.join(dat, "simcells.v")
    if not os.path.isfile(path):
        raise InfraError(f"no {path} (Yosys's simulation models of its gate cells)")
    return path


def trusted_files():
    """What this stage executes or reads besides the submission: by content."""
    return [SVEVAL, os.path.abspath(__file__), simcells()]


def tool_paths():
    """The simulator's files (by metadata, for check.py's integrity tripwire):
    the Verilator scripts and binaries, its whole VERILATOR_ROOT (the runtime
    sources and headers every model is compiled against), the C++ compiler and
    make. Tools that are missing are left out; the stage itself reports them."""
    out = []
    for name in ("verilator", "verilator_bin"):
        p = shutil.which(name)
        if p:
            out.append(os.path.realpath(p))
    try:
        out.append(verilator_info()[2])
    except InfraError:
        pass
    for name in (os.environ.get("CXX") or "c++", "make"):
        p = shutil.which(name)
        if p:
            out.append(os.path.realpath(p))
            xc = shutil.which("xcrun")      # macOS: /usr/bin/c++ is a shim for the real one
            if xc:
                r = subprocess.run([xc, "--find", name], capture_output=True, text=True,
                                   env=sandbox.scrubbed_env())
                if r.returncode == 0 and r.stdout.strip():
                    out.append(os.path.realpath(r.stdout.strip()))
    return out


# ---------------------------------------------------------------- the netlist

def reread_netlist(netlist, top, work):
    """A fresh Yosys process reads the netlist with the cell models as a library: (the top module's cells by type,
    its `ltp -noff` depth, Yosys's JSON view of the whole design, `write_json`; the JSON of the netlist's own modules,
    written before the library is read; the JSON of the design after `insbuf`). Raises score.ScoreError. The first
    JSON is Yosys's own reading of the netlist, every assign alias resolved (`unknown_bits`, `netlist_ports`); Yosys
    refuses to write it for a module that still holds processes, which a netlist the pinned flow wrote never does.
    The second shows the attributes the netlist gives its modules (`opaque_parts`; `-noblackbox`: an empty module
    stays an empty module, not a box Yosys made of it). In the third, written after
    `stat` and `ltp`, every assign is a buffer cell of its own (type `$_BUF_`, which no netlist text can name: an
    instance written `\\$_BUF_` has type `\\$_BUF_`), so a bit's drivers can be counted (`conflicting_drivers`)."""
    d = os.path.join(work, "reread")
    os.makedirs(d, exist_ok=True)
    st, lt, js = os.path.join(d, "stat.json"), os.path.join(d, "ltp.txt"), os.path.join(d, "netlist.json")
    own_js, drv_js = os.path.join(d, "own.json"), os.path.join(d, "drivers.json")
    score.run_yosys(score.yosys_bin(), f'read_verilog -noblackbox "{netlist}"\nwrite_json "{own_js}"\n'
                    f'read_verilog -lib "{simcells()}"\nhierarchy -top {top}\nwrite_json "{js}"\n'
                    f'tee -q -o "{st}" stat -json\ntee -q -o "{lt}" ltp -noff\n'
                    f'insbuf\nwrite_json "{drv_js}"\n', d,
                    reads=[netlist, simcells()])
    views = []
    for path in (js, own_js, drv_js):
        with open(path) as fh:
            views.append(json.load(fh))
    design, own, drivers = views
    return score.parse_stat(st, top), score.parse_ltp(lt), design, own, drivers


BOX_ATTRIBUTES = ("blackbox", "whitebox", "lib_whitebox")      # Yosys's attributes of a module it treats as a box


def opaque_parts(own, design):
    """The parts of a netlist the unknown-constant rule cannot look into, as refusal phrases: a module the netlist
    defines with a box attribute (BOX_ATTRIBUTES, whatever its value: `own`, the netlist's modules as read before
    the library), and a cell, in any module that is not a library model, whose type is no module of `design` (an
    unknown cell type, or a cell Yosys made from an expression: the pinned flow writes gate instances only). With
    the netlist's own boxes refused, every box module of `design` is one of `simcells.v`'s gate models."""
    out = []
    for mname, mod in sorted(own.get("modules", {}).items()):
        attrs = sorted(a for a in (mod.get("attributes") or {}) if a in BOX_ATTRIBUTES)
        if attrs:
            out.append(f"it defines module `{mname.lstrip(chr(92))}` with the attribute "
                       f"{_and(f'`{a}`' for a in attrs)} (the check cannot see what a box computes)")
    mods = design.get("modules", {})
    for mname, mod in sorted(mods.items()):
        if (mod.get("attributes") or {}).get("blackbox") is not None:
            continue
        where = "" if (mod.get("attributes") or {}).get("top") else f" of module `{mname.lstrip(chr(92))}`"
        for cname, c in sorted((mod.get("cells") or {}).items()):
            ctype = str(c.get("type", "?"))
            if ctype in mods:
                continue
            if cname.startswith("$"):        # a name Yosys made: a cell of an expression (`assign y = a & b;`)
                m = SRC_LINE.search(str((c.get("attributes") or {}).get("src", "")))
                at = f" at netlist line {m.group(1)}" if m else ""
                out.append(f"it has a `{ctype}` cell{where} that Yosys made from an expression{at} (the pinned "
                           "flow writes gate instances only)")
            else:
                out.append(f"its `{ctype.lstrip(chr(92))}` cell `{cname}`{where} is neither a gate of Yosys's cell "
                           "library nor a module the netlist defines")
    return out


ALIAS = "$_BUF_"      # the cell type `insbuf` gives each assign in the third view of `reread_netlist`


def _alias_graph(mod):
    """Of one module of the `insbuf` view: (alias cells as (A, Y) bit pairs, the bits that hold an unknown value
    through assigns: a constant `x`/`z` assigned to them, or a bit assigned from one of those)."""
    pairs = []
    for c in (mod.get("cells") or {}).values():
        if c.get("type") == ALIAS:
            conn = c.get("connections") or {}
            pairs += list(zip(conn.get("A", []), conn.get("Y", [])))
    unknown = {y for a, y in pairs if a in UNKNOWN}
    grew = True
    while grew:
        grew = False
        for a, y in pairs:
            if a in unknown and y not in unknown:
                unknown.add(y)
                grew = True
    return pairs, unknown


def _names_of(mod, bits):
    """(the net bits of a module, `_bit_names` form, whose JSON bit is in `bits`, names Yosys did not hide first;
    their declaration lines)."""
    out, lines = [], set()
    for net, e in sorted(mod.get("netnames", {}).items(), key=lambda kv: (kv[0].startswith("$"), kv[0])):
        b = e.get("bits", [])
        idx = [declared_index(e, i) for i, x in enumerate(b) if x in bits]
        if idx:
            out += _bit_names(net, len(b), idx)
            m = SRC_LINE.search(str((e.get("attributes") or {}).get("src", "")))
            if m:
                lines.add(int(m.group(1)))
    return out, sorted(lines)


def conflicting_drivers(drivers):
    """Refusal phrases for the net bits of the `insbuf` view (`reread_netlist`) that have more than one driver of
    which one is an unknown value (an assign of a constant `x`/`z`, or of a bit that holds one through assigns). A
    driver is an input or inout port, an output or inout cell pin (a pin of unknown direction counts too), or an
    assign. Every module that is not a library model is read."""
    out = []
    for mname, mod in sorted(drivers.get("modules", {}).items()):
        attrs = mod.get("attributes") or {}
        if attrs.get("blackbox") is not None:
            continue
        pairs, unknown = _alias_graph(mod)
        count, bad = {}, set()
        for p in (mod.get("ports") or {}).values():
            if p.get("direction") in ("input", "inout"):
                for b in p.get("bits", []):
                    count[b] = count.get(b, 0) + 1
        for c in (mod.get("cells") or {}).values():
            dirs = c.get("port_directions") or {}
            for pin, conn in (c.get("connections") or {}).items():
                if dirs.get(pin) in ("output", "inout", None):
                    for b in conn:
                        if not isinstance(b, str):
                            count[b] = count.get(b, 0) + 1
        for a, y in pairs:
            if a in UNKNOWN or a in unknown:
                bad.add(y)
        hit = {b for b in bad if count.get(b, 0) > 1}
        if hit:
            names, lines = _names_of(mod, hit)
            where = "" if attrs.get("top") else f" of module `{mname.lstrip(chr(92))}`"
            at = f" (declared at netlist line{'s' if len(lines) > 1 else ''} {_and(map(str, lines))})" if lines else ""
            out.append(f"it drives {_and(names or ['a bit with no name'])}{where}{at} from more than one place, and "
                       "one of the drivers is an unknown value (Yosys's view of the netlist keeps one driver of a "
                       "bit, so it can hide the unknown one)")
    return out


# The cells through which no combinational path runs: the one flip-flop the pinned clocked flow writes
# (`dfflegalize -cell $_DFF_P_ x`, score/svgolf_seq.ys). Every other cell, of any type (a gate, a buffer `insbuf`
# made of an assign, a cell of a type nothing defines), counts as combinational from each input pin to each output
# pin, and a pin of unknown direction or an inout as both: that can only find more loops, never fewer.
LOOP_BREAKERS = ("$_DFF_P_",)


def _cycles(succ):
    """The strongly connected components of the graph `succ` (node -> set of nodes) that hold a cycle: more than one
    node, or one node with an edge to itself, each as a sorted list. Tarjan's algorithm, iterative (a netlist has
    10^5 bits), visiting the nodes in sorted order so that the result does not depend on dictionary order."""
    index, low, on, stack, out, n = {}, {}, set(), [], [], 0
    for root in sorted(succ):
        if root in index:
            continue
        index[root] = low[root] = n
        n += 1
        stack.append(root)
        on.add(root)
        work = [(root, iter(sorted(succ.get(root, ()))))]
        while work:
            v, it = work[-1]
            for w in it:
                if w not in index:
                    index[w] = low[w] = n
                    n += 1
                    stack.append(w)
                    on.add(w)
                    work.append((w, iter(sorted(succ.get(w, ())))))
                    break
                if w in on:
                    low[v] = min(low[v], index[w])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == index[v]:
                    comp = []
                    while True:
                        w = stack.pop()
                        on.discard(w)
                        comp.append(w)
                        if w == v:
                            break
                    if len(comp) > 1 or v in succ.get(v, ()):
                        out.append(sorted(comp))
    return out


def comb_loops(drivers):
    """Refusal phrases for the combinational loops of the `insbuf` view (`reread_netlist`), found BIT BY BIT: a node
    per net bit, an edge from each bit on an input pin of a cell to each bit on its output pins (LOOP_BREAKERS aside;
    in this view every assign is a buffer cell, so an assign is an edge too), and a cycle of bits is a loop. Two bits
    of one vector, one assigned from the other, make no loop here; Verilator's UNOPTFLAT, which looks at whole
    vectors, calls them one (NETLIST_WNO). Every module that is not a library model is read."""
    out = []
    for mname, mod in sorted(drivers.get("modules", {}).items()):
        attrs = mod.get("attributes") or {}
        if attrs.get("blackbox") is not None:
            continue
        succ = {}
        for c in (mod.get("cells") or {}).values():
            if str(c.get("type", "")).lstrip("\\") in LOOP_BREAKERS:
                continue
            dirs = c.get("port_directions") or {}
            ins, outs = set(), set()
            for pin, conn in (c.get("connections") or {}).items():
                bits = {b for b in conn if not isinstance(b, str)}
                if dirs.get(pin) != "output":
                    ins |= bits
                if dirs.get(pin) != "input":
                    outs |= bits
            for a in ins:
                succ.setdefault(a, set()).update(outs)
        where = "" if attrs.get("top") else f" of module `{mname.lstrip(chr(92))}`"
        for comp in _cycles(succ):
            names, lines = _names_of(mod, set(comp))
            at = f" (declared at netlist line{'s' if len(lines) > 1 else ''} {_and(map(str, lines))})" if lines else ""
            out.append(f"it has a combinational loop through {_and(names or ['net bits with no name'])}{where}{at}")
    return out


def read_unknown(drivers, top=None):
    """{(module, net, declared bit)} of the nets of the `insbuf` view that hold an unknown value through assigns AND
    reach something that reads them: a cell pin that is not an output (other than an assign's own), or a port that
    is not an input, directly or through further assigns. For the refusal's message only (`unknown_message`): the
    verdict is `unknown_bits`', on the first view."""
    out = set()
    for mname, mod in sorted(drivers.get("modules", {}).items()):
        if (mod.get("attributes") or {}).get("blackbox") is not None:
            continue
        pairs, unknown = _alias_graph(mod)
        read = set()
        for c in (mod.get("cells") or {}).values():
            if c.get("type") == ALIAS:
                continue
            dirs = c.get("port_directions") or {}
            for pin, conn in (c.get("connections") or {}).items():
                if dirs.get(pin) != "output":
                    read |= {b for b in conn if b in unknown}
        for p in (mod.get("ports") or {}).values():
            if p.get("direction") != "input":
                read |= {b for b in p.get("bits", []) if b in unknown}
        grew = True
        while grew:
            grew = False
            for a, y in pairs:
                if y in read and a in unknown and a not in read:
                    read.add(a)
                    grew = True
        name = mname if top is not None and mname != top else None
        for net, e in mod.get("netnames", {}).items():
            for i, x in enumerate(e.get("bits", [])):
                if x in read:
                    out.add((name, net, declared_index(e, i)))
    return out


def reread_check(netlist, top, sres, work):
    """The written netlist IS the scored one: a fresh Yosys process reads it
    (one gate instance per scored cell) with the cell models as a library and
    must count exactly the scored gates by type, and the scored depth; before
    that, the netlist must have no part the unknown-constant rule cannot look
    into (`opaque_parts`), no bit driven twice with an unknown value
    (`conflicting_drivers`) and no combinational loop, bit by bit
    (`comb_loops`). Returns Yosys's JSON view of the netlist and the `insbuf`
    view (`reread_netlist`)."""
    try:
        cells, depth, design, own, drivers = reread_netlist(netlist, top, work)
    except (score.ScoreError, OSError, ValueError) as e:
        raise Reject(f"the scored netlist does not re-read: {e}")
    why = opaque_parts(own, design) + conflicting_drivers(drivers) + comb_loops(drivers)
    if why:
        raise Reject("the netlist is refused before it is simulated: " + _and(why) + ". check.py --keep keeps the "
                     "netlist (the result's `postsynth_dir`)")
    got = {}
    for c, n in cells.items():
        m = re.fullmatch(r"\\?\$_(\w+?)_", c)
        got[m.group(1) if m else c] = n
    want = dict(sres["gates"])
    # (a clocked netlist's flops re-read as library instances, which `ltp -noff` does not skip: its
    # depth is cross-checked by the ppa stage instead, which must find the scored `ltp -noff` depth)
    if got != want or (depth != sres["depth"] and sres.get("flow") != "seq"):
        raise Reject(f"the netlist file does not re-read as the scored netlist: gates {got}, "
                     f"depth {depth}; the score has gates {want}, depth {sres['depth']}")
    return design, drivers


def netlist_ports(design, top):
    """{(direction, name, width)} of module `top` in Yosys's JSON view of the netlist (`reread_netlist`)."""
    mod = design.get("modules", {}).get(top)
    if mod is None:
        raise Reject(f"the netlist has no module `{top}`")
    ports = {(p["direction"], name, len(p["bits"])) for name, p in mod.get("ports", {}).items()}
    if any(d == "inout" for d, _, _ in ports):
        raise Reject("the netlist has an inout port (a combinational task has inputs and outputs)")
    return ports


UNKNOWN = ("x", "z")      # an unknown-valued constant bit in Yosys's JSON (`"x"`, `"z"`; a signal bit is a number)
SRC_LINE = re.compile(r":(\d+)\.\d+-\d+\.\d+$")


def declared_index(entry, i):
    """The declared index of bit `i` (LSB first) of a JSON net or port `entry` (its `offset` and `upto`)."""
    n, off = len(entry.get("bits", [])), int(entry.get("offset", 0))
    return off + (n - 1 - i if entry.get("upto") else i)


def unknown_bits(design, top=None):
    """Where Yosys's JSON view of the netlist (`reread_netlist`) holds an unknown-valued constant, in EVERY module
    that is not a library model (simcells.v, read with -lib, is all blackboxes): (unread, readers).
    `unread`: every net with such a bit, [{"net", "width", "bits", "value", "line"}]: `bits` the declared indices
    of those bits, `value` "x", "z" or "x/z", `line` the netlist line of the net's DECLARATION (its `src`
    attribute; None without one), and `module` when it is not `top`. `readers`: every place that READS one: a cell
    pin whose direction is input, inout or not known (fail closed), {"kind": "cell", "cell", "type", "pin",
    "bits"} (`bits`: the pin's bit positions, empty for a one-bit pin), and a port that is not an input (output,
    inout, or of unknown direction), {"kind": "port", "port", "direction", "width", "bits"} (declared indices).
    Yosys resolves every assign alias in this view, so a constant bit is "x" or "z" wherever it is connected: a
    wire `v` assigned from `w[0] = 1'hx` and read by a gate shows the x on the gate's pin."""
    unread, readers = [], []
    for mname, mod in sorted(design.get("modules", {}).items()):
        if (mod.get("attributes") or {}).get("blackbox"):
            continue
        where = {} if top is None or mname == top else {"module": mname}
        for net, e in sorted(mod.get("netnames", {}).items()):
            b = e.get("bits", [])
            hit = [i for i, x in enumerate(b) if x in UNKNOWN]
            if hit:
                m = SRC_LINE.search(str((e.get("attributes") or {}).get("src", "")))
                unread.append(dict(where, net=net, width=len(b), bits=[declared_index(e, i) for i in hit],
                                   value="/".join(sorted({b[i] for i in hit})),
                                   line=int(m.group(1)) if m else None))
        for cname, c in sorted(mod.get("cells", {}).items()):
            dirs = c.get("port_directions") or {}
            for pin, conn in sorted((c.get("connections") or {}).items()):
                if dirs.get(pin) == "output":
                    continue
                hit = [i for i, x in enumerate(conn) if x in UNKNOWN]
                if hit:
                    readers.append(dict(where, kind="cell", cell=cname, type=str(c.get("type", "?")).lstrip("\\"),
                                        pin=pin, bits=hit if len(conn) > 1 else []))
        for pname, p in sorted(mod.get("ports", {}).items()):
            if p.get("direction") == "input":
                continue
            b = p.get("bits", [])
            hit = [i for i, x in enumerate(b) if x in UNKNOWN]
            if hit:
                readers.append(dict(where, kind="port", port=pname, direction=p.get("direction"), width=len(b),
                                    bits=[declared_index(p, i) for i in hit]))
    return unread, readers


def _and(items, cap=5):
    """'a', 'a and b', 'a, b and c', at most `cap` of them, then 'and N more'."""
    items = list(items)
    if len(items) > cap:
        return ", ".join(items[:cap]) + f" and {len(items) - cap} more"
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " and " + items[-1]


def _bit_names(net, width, bits):
    return [f"`{net}`" if width == 1 and bits == [0] else f"`{net}[{k}]`" for k in bits]


def _bits(bits):
    """'bit 0', 'bits 0 and 1', 'bits 0, 1, 2, 3, 4 and 11 more'."""
    return ("bit " if len(bits) == 1 else "bits ") + _and(map(str, bits))


def _of(r):
    return f" of module `{r['module']}`" if "module" in r else ""


# The four lines of score/canon.ys that strip the design's names (`src`, private and numbered names); the naming run
# drops them, so that the netlist it writes keeps the names of the source.
NAME_STRIPPING = ("setattr -unset src", "setattr -mod -unset src", "rename -hide", "rename -enumerate")
NAMING_TIMEOUT_S = 120


def unknown_names(sres, timeout=NAMING_TIMEOUT_S):
    """A NAMING run, made only when the check refuses an unknown constant, to say where it came from in the player's
    words; it never decides anything. The scored run's own sources, gating, point and flow (`sres`, score.py's
    result: `sources`, `gated`, `top`, `params`, `flow`), through score/canon.ys without NAME_STRIPPING and the flow's
    script (svgolf.ys, or svgolf_seq.ys for a clocked one) up to and including its last `opt_clean`, then
    `write_json`, in the sandbox like every Yosys run and within `timeout` seconds. Returns the sorted names of the
    bits that hold an unknown value under a name Yosys did not make up (`t[0]`), or None when the run fails or has
    none to give. Its cells can differ from the scored run's (names change Yosys's choices), which is why it only
    names."""
    work = tempfile.mkdtemp(prefix="svgolf-xnames-")
    try:
        sources = [s["path"] for s in sres.get("sources") or []]
        if not sources:
            return None
        if sres.get("gated", True):
            read, _ = score.gate_sources(sources, work)
        else:
            read = list(sources)
        il, js = os.path.join(work, "named.il"), os.path.join(work, "named.json")
        canon = [ln for ln in score.render_canon(read, sres["top"], sres["params"], il).splitlines()
                 if ln.strip() not in NAME_STRIPPING]
        script = score.FLOWS["seq" if sres.get("flow") == "seq" else "comb"][0]
        synth = score.render_script(il, sres["top"], os.path.join(work, "stat.json"), os.path.join(work, "ltp.txt"),
                                    os.path.join(work, "netlist.v"), script).splitlines()
        last = [k for k, ln in enumerate(synth) if ln.strip().startswith("opt_clean")]
        if len(last) != 1:
            return None
        yosys = score.yosys_bin()
        for name, lines in (("canon", canon), ("named", synth[:last[0] + 1] + [f'write_json "{js}"'])):
            path = os.path.join(work, f"{name}.ys")
            with open(path, "w") as fh:
                fh.write("\n".join(lines) + "\n")
            proc = score.yosys_run([yosys, "-q", "-l", os.path.join(work, f"{name}.log"), "-s", path], yosys, work,
                                   read, timeout, label="yosys (naming run)")
            if proc.returncode != 0:
                return None
        with open(js) as fh:
            design = json.load(fh)
        names = set()
        for mod in design.get("modules", {}).values():
            if (mod.get("attributes") or {}).get("blackbox"):
                continue
            for net, e in mod.get("netnames", {}).items():
                if e.get("hide_name") or net.startswith("$"):
                    continue
                b = e.get("bits", [])
                for i, x in enumerate(b):
                    if x in UNKNOWN:
                        names.add(net if len(b) == 1 and not e.get("offset") else f"{net}[{declared_index(e, i)}]")
        def key(n):        # `y[2]` before `y[10]`
            base, _, k = n.partition("[")
            return (base, int(k.rstrip("]")) if k.rstrip("]").lstrip("-").isdigit() else -1, n)
        return sorted(names, key=key) or None
    except (OSError, ValueError, KeyError, TypeError, score.ScoreError, subprocess.SubprocessError):
        return None
    finally:
        shutil.rmtree(work, ignore_errors=True)


def unknown_message(unread, readers, names=None, read=None):
    """The refusal of a netlist whose unknown-valued constant something reads (`unknown_bits`), or None when
    nothing does: the netlist's wires that hold the constant (names Yosys did not hide first, up to five), the
    readers (up to five, then "and N more"), with `names` (`unknown_names`, when the naming run gave some) the
    bits in the source's own words, and how to look at the netlist. With `read` (`read_unknown`: the net bits of
    the `insbuf` view that something reads) only those wires are named: Yosys's first view gives a constant no
    identity, so without it every wire that holds an unknown value is named, read or not."""
    if not readers:
        return None
    if read is not None:
        kept = []
        for u in unread:
            bits = [k for k in u["bits"] if (u.get("module"), u["net"], k) in read]
            if bits:
                kept.append(dict(u, bits=bits))
        unread = kept
    said = (f". In a run that keeps your signal names, the unknown bits are {_and(f'`{n}`' for n in names)}"
            if names else "")
    tail = (f": a 2-state simulation would read it as a fixed 0 or 1{said}. check.py --keep keeps the netlist (the "
            "result's `postsynth_dir`)")

    def reader(r):
        if r["kind"] == "cell":
            bits = f", {_bits(r['bits'])}" if r["bits"] else ""
            return f"the `{r['type']}` cell `{r['cell']}`{_of(r)} (pin {r['pin']}{bits})"
        what = r["direction"] if r["direction"] in ("output", "inout") else "port"
        bits = "" if r["width"] == 1 else f" ({_bits(r['bits'])})"
        return f"the {what} `{r['port']}`{_of(r)}{bits}"

    nets = sorted(unread, key=lambda u: (u["net"].startswith("$"), u["net"]))
    if not nets:      # the constant sits on the readers themselves (a literal on a pin or a port bit)
        def on(r):
            if r["kind"] == "cell":
                bits = f", {_bits(r['bits'])}" if r["bits"] else ""
                return f"the `{r['type']}` cell `{r['cell']}`{_of(r)} has an unknown value on pin {r['pin']}{bits}"
            return f"{reader(r)} is an unknown value"
        return "the netlist reads an unknown value: " + _and(on(r) for r in readers) + tail
    held = _and(b for u in nets for b in _bit_names(u["net"], u["width"], u["bits"]))
    lines = sorted({u["line"] for u in nets if u["line"] is not None})
    at = f" (declared at netlist line{'s' if len(lines) > 1 else ''} {_and(map(str, lines))})" if lines else ""
    return f"the netlist ties {held}{at} to an unknown value, and it is read by {_and(map(reader, readers))}" + tail


def unread_note(unread):
    """The stderr line of an accepted netlist that ties bits to an unknown value nothing reads."""
    held = _and(b for u in unread for b in _bit_names(u["net"], u["width"], u["bits"]))
    return (f"postsynth: the netlist ties {held} to an unknown value that nothing reads (Yosys leaves one, for "
            "example, where it removed an unused register bit): accepted")


# ---------------------------------------------------------------- vectors

def fixed_vectors(ins, corners):
    """all-0, all-1, walking ones/zeros (the others all-0 / all-1), task corners."""
    full = {n: (1 << w) - 1 for n, w in ins}
    zero = {n: 0 for n, _ in ins}
    vs = [dict(zero), dict(full)]
    for n, w in ins:
        for b in range(w):
            for base in (zero, full):
                v1 = dict(base)
                v1[n] = 1 << b
                v0 = dict(base)
                v0[n] = full[n] ^ (1 << b)
                vs += [v1, v0]
    nfixed = len(vs)
    unknown = sorted(set(corners) - set(full))
    if unknown:
        raise InfraError(f"task.json `postsynth.corners` names {unknown}, not input ports")
    if corners:
        lists = [[int(x, 0) if isinstance(x, str) else int(x) for x in corners[n]]
                 if n in corners else [0, full[n]] for n, _ in ins]
        for combo in itertools.product(*lists):
            vs.append({n: v & full[n] for (n, _), v in zip(ins, combo)})
    return vs, nfixed


# The fills of one harvested assignment, in the order `harvest_vectors` lists
# them: the free bits all-0, all-1, random, random. The light mode keeps the
# first two (`light_select`).
HARVEST_FILLS = ("0", "1", "r", "r")


def harvest_vectors(canon_sv, top, params, ins, work, rng, cap_pairs):
    """Vectors from the comparison constants of Yosys's coarse design (see the
    module docstring): `len(HARVEST_FILLS)` consecutive vectors per distinct
    assignment, the single assignments first, then the compatible pairs.
    Returns (vectors, number of distinct assignments)."""
    chp = "".join(f" -chparam {k} {v}" for k, v in params.items())
    d = os.path.join(work, "harvest")
    os.makedirs(d, exist_ok=True)
    js = os.path.join(d, "coarse.json")      # inside the one directory the sandboxed Yosys may write
    try:
        score.run_yosys(score.yosys_bin(), f'read_verilog -sv "{canon_sv}"\n'
                        f'hierarchy -check -top {top}{chp}\nproc\nflatten\nopt -purge\n'
                        f'write_json "{js}"\n', d, reads=[canon_sv])
    except score.ScoreError as e:
        raise Reject(f"Yosys cannot build the coarse design for constant harvesting: {e}")
    with open(js) as fh:
        mods = json.load(fh)["modules"]
    mod = mods.get(top) or next((m for k, m in mods.items() if k.lstrip("\\") == top), None)
    if mod is None:
        raise Reject(f"the coarse design has no module `{top}`")
    width = dict(ins)
    bitmap = {}
    for pn, pd in mod["ports"].items():
        if pd["direction"] == "input" and pn in width:
            for i, b in enumerate(pd["bits"]):
                bitmap[b] = (pn, i)
    assigns = []
    for c in mod["cells"].values():
        if c["type"] not in CMP_CELLS:
            continue
        a, b = c["connections"].get("A", []), c["connections"].get("B", [])
        for k, o in ((a, b), (b, a)):
            # A constant operand: every bit a string. Its 0/1 bits are the
            # assignment; an x/z bit (a don't-care to Yosys) leaves that input
            # bit free, so a comparison against `32'hDEAD_BEEz` still steers
            # vectors into the 2^-28 region it selects.
            if k and all(isinstance(x, str) for x in k) and any(x in ("0", "1") for x in k):
                val = [int(x) if x in ("0", "1") else None for x in k]     # LSB first
                if o and all(x in bitmap for x in o):
                    asg = {}
                    for x, v in zip(o, val):
                        if v is not None:
                            pn, i = bitmap[x]
                            asg.setdefault(pn, {})[i] = v
                    assigns.append(asg)
                else:
                    for pn, w in ins:
                        assigns.append({pn: {i: v for i, v in enumerate(val[:w])
                                             if v is not None}})
    uniq = []
    for a in assigns:
        if a not in uniq:
            uniq.append(a)

    def fill(asg):
        out = []
        for mode in HARVEST_FILLS:
            v = {}
            for pn, w in ins:
                base = 0 if mode == "0" else ((1 << w) - 1 if mode == "1" else rng.getrandbits(w))
                for i, bit in asg.get(pn, {}).items():
                    base = (base & ~(1 << i)) | (bit << i)
                v[pn] = base
            out.append(v)
        return out

    vecs, pairs = [], 0
    for a in uniq:
        vecs += fill(a)
    for i in range(len(uniq)):
        for j in range(i + 1, len(uniq)):
            if pairs >= cap_pairs:
                break
            m, ok = {pn: dict(dd) for pn, dd in uniq[i].items()}, True
            for pn, dd in uniq[j].items():
                for bit, v in dd.items():
                    if m.setdefault(pn, {}).get(bit, v) != v:
                        ok = False
                    m[pn][bit] = v
            if ok:
                vecs += fill(m)
                pairs += 1
    return vecs, len(uniq)


def spread(items, n):
    """At most `n` of `items`, evenly spaced, the first one always kept."""
    if n <= 0:
        return []
    if len(items) <= n:
        return list(items)
    return [items[i * len(items) // n] for i in range(n)]


def light_select(fixed, nfixed, harvest, nuniq, rand, total):
    """The LIGHT vector set (module docstring, "TWO MODES"): a deterministic
    subset of `fixed + harvest + rand`, at most `total` vectors before the
    duplicates drop. `fixed` is `fixed_vectors`' list (`nfixed` generic
    vectors, all-0 and all-1 first, then the task corners), `harvest` is
    `harvest_vectors`' list with `nuniq` single assignments, `rand` the full
    random stream. Returns (vectors, counts), counts = the vectors taken per
    class (`fixed`, `task_corners`, `harvest_vectors`, `random`)."""
    base = fixed[:2]
    quota = max(1, (total - len(base)) // 4)
    walking = spread(fixed[2:nfixed], quota)
    corners = spread(fixed[nfixed:], quota)
    f = len(HARVEST_FILLS)
    blocks = len(harvest) // f

    def zero_one(rng):
        return [harvest[b * f + j] for b in rng for j in (0, 1)]

    hv = spread(zero_one(range(min(nuniq, blocks))), quota)
    if len(hv) < quota:
        hv += spread(zero_one(range(nuniq, blocks)), quota - len(hv))
    k = max(0, total - len(base) - len(walking) - len(corners) - len(hv))
    rnd = rand[:k]
    counts = {"fixed": len(base) + len(walking), "task_corners": len(corners),
              "harvest_vectors": len(hv), "random": len(rnd)}
    return base + walking + corners + hv + rnd, counts


def dedup(ins, vecs):
    seen, out = set(), []
    for v in vecs:
        k = tuple(v[n] for n, _ in ins)
        if k not in seen:
            seen.add(k)
            out.append(v)
    return out


# ---------------------------------------------------------------- evaluators

def lssv_eval(envl, point_s, ins, vecs, fuel, work, deadline, trace=False, start=None):
    if not os.path.isfile(SVEVAL):
        raise InfraError(f"{SVEVAL} is not built (`lake build svgolf-eval`, part of check.py's "
                         "trusted stage)")
    ld = os.path.join(work, "lssv")        # the one directory the sandboxed evaluator may write
    os.makedirs(ld, exist_ok=True)
    vp, op = os.path.join(ld, "lssv.vec"), os.path.join(ld, "lssv.out")
    with open(vp, "w") as fh:
        for v in vecs:
            fh.write(" ".join(f"{n}={v[n]:x}" for n, _ in ins) + "\n")
    t0 = time.time()
    try:
        p = sandbox.run([SVEVAL] + ["--trace"] * trace + (["--start", start] if trace and start else [])
                        + [envl, point_s, vp, op, str(fuel)],
                        sandbox.exec_spec(SVEVAL, read=[os.path.dirname(os.path.abspath(envl)), ld], write=[ld],
                                          label="svgolf-eval"),
                        env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"} if sandbox.policy().active else None,
                        cwd=ld, timeout=max(1.0, deadline - time.time()), kind="tool", label="svgolf-eval")
    except subprocess.TimeoutExpired:
        raise Reject(f"the ls-sv evaluation of {len(vecs)} vectors did not finish within the "
                     "task's `postsynth.time_limit_s` (fail closed)")
    el = time.time() - t0
    if p.returncode != 0:
        msg = (p.stderr + p.stdout).strip()[-2000:]
        # Without vectors, svgolf-eval still prints the instantiated design's
        # header: an unsupported construct can leave it without the ports.
        ep, eo = os.path.join(ld, "lssv.empty.vec"), os.path.join(ld, "lssv.empty.out")
        open(ep, "w").close()
        q = sandbox.run([SVEVAL, envl, point_s, ep, eo],
                        sandbox.exec_spec(SVEVAL, read=[os.path.dirname(os.path.abspath(envl)), ld], write=[ld],
                                          label="svgolf-eval"),
                        env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"} if sandbox.policy().active else None,
                        cwd=ld, timeout=60, kind="tool", label="svgolf-eval")
        head = open(eo).read() if q.returncode == 0 and os.path.isfile(eo) else ""
        if "unsupported=true" in head:
            raise Reject("ls-sv does not support this design: it loads with an unsupported "
                         f"node ({head.splitlines()[-2] if len(head.splitlines()) > 1 else head}"
                         f"), and svgolf-eval cannot run it ({msg[-300:]}). This is an ls-sv "
                         "limit, not a disagreement: no proof about such a design can hold. "
                         "Rewrite it without the construct, or add the construct to ls-sv by "
                         "PR (README.md, \"Rules\").")
        raise Reject("ls-sv cannot evaluate the design at the scoring point: " + msg)
    ports, rows, design, timing = set(), {}, None, None
    with open(op) as fh:
        for ln in fh:
            f = ln.split()
            if not f:
                continue
            if f[0] == "PORT":
                ports.add(({"in": "input", "out": "output"}[f[2]], f[1], int(f[3])))
            elif f[0] == "DESIGN":
                design = ln.strip()
            elif f[0] == "TIME":
                timing = ln.strip()
            elif f[0] == "V":
                bar = f.index("|")
                rows[int(f[1])] = (dict(x.split("=", 1) for x in f[2:bar]),
                                   dict(x.split("=", 1) for x in f[bar + 1:]))
            elif f[0] == "E":
                rows[int(f[1])] = ("ERROR", " ".join(f[2:]))
    return ports, [rows.get(i, ("ERROR", "no result")) for i in range(len(vecs))], design, \
        timing, el


# Verilator's lint is run with -Wall and every warning FATAL, minus these three,
# each of which cannot change a value the harness reads. Everything else
# rejects (measured on mutated netlists, 2026-10-29: UNDRIVEN, PINMISSING,
# PINCONNECTEMPTY, MULTIDRIVEN, WIDTHTRUNC, an unknown cell): a net or a pin
# nothing drives would be a silent 0 in a 2-state simulator.
NETLIST_WNO = (
    # the netlist is `netlist.v` and the cell library `simcells.v`: neither
    # file is named after its modules, and `\$_AND_ ` could not be a file name
    "DECLFILENAME",
    # a design that never reads some input bit: the bit exists, nothing
    # depends on it (a mutated netlist that drops all uses of `a[15]` is
    # otherwise rejected)
    "UNUSEDSIGNAL",
    # a loop at the granularity of a whole vector (2026-11-13). `reread_check`
    # has already refused every real combinational loop bit by bit
    # (`comb_loops`), so what Verilator still calls circular is a vector one of
    # whose bits is assigned from another (Yosys's merged flip-flops), which it
    # simulates correctly, only more slowly; logic that does not settle stops
    # the model (DIDNOTCONVERGE), and the run is rejected
    "UNOPTFLAT",
)
# The RTL third opinion is the PLAYER'S source; any construct Verilator
# accepts at all (with warnings) is simulated, because it never decides the
# verdict, only illustrates a rejection.
RTL_FLAGS = ("-Wno-fatal", "-Wno-lint", "-Wno-style", "-Wno-DECLFILENAME")
# Deterministic two-state values for everything Verilog leaves unknown.
VL_X_FLAGS = ("--x-assign", "0", "--x-initial", "0")
# One C++ file per run is small (the 1400-gate netlists compile in seconds);
# -O1 keeps the model fast without the long compile of -Os/-O3. No compiler
# cache is used (OBJCACHE is emptied below): every run builds from source.
VL_CFLAGS = "-O1"
VL_JOBS = os.environ.get("SVGOLF_VERILATOR_JOBS", "2")
VL_PREFIX = "VNET"

HARNESS = r"""// generated by check/postsynth.py -- the Verilator harness of one postsynth run
#include "%(prefix)s.h"
#include "verilated.h"
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
#include <type_traits>

// A hex token as little-endian 32-bit words. False unless it is hex and has no
// bit at or above `width`.
static bool parse_hex(const char* s, uint32_t* w, int nw, int width) {
  for (int i = 0; i < nw; ++i) w[i] = 0;
  const size_t n = strlen(s);
  if (n == 0) return false;
  for (size_t i = 0; i < n; ++i) {
    const char c = s[n - 1 - i];
    unsigned v;
    if (c >= '0' && c <= '9') v = c - '0';
    else if (c >= 'a' && c <= 'f') v = c - 'a' + 10;
    else if (c >= 'A' && c <= 'F') v = c - 'A' + 10;
    else return false;
    if (v == 0) continue;
    if (4 * i >= (size_t)nw * 32) return false;
    w[i / 8] |= v << (4 * (i %% 8));
  }
  for (int b = width; b < nw * 32; ++b)
    if ((w[b / 32] >> (b %% 32)) & 1) return false;
  return true;
}

static void put_bits(std::string& out, const uint32_t* w, int width) {
  for (int b = width - 1; b >= 0; --b) out += ((w[b / 32] >> (b %% 32)) & 1) ? '1' : '0';
}

int main(int argc, char** argv) {
  if (argc != 2) { fprintf(stderr, "usage: harness VECTORS\n"); return 2; }
  FILE* fp = fopen(argv[1], "r");
  if (!fp) { fprintf(stderr, "cannot open %%s\n", argv[1]); return 2; }
  const std::unique_ptr<VerilatedContext> ctx{new VerilatedContext};
  ctx->randReset(0);
  const std::unique_ptr<%(prefix)s> top{new %(prefix)s{ctx.get(), "TOP"}};
  char tok[4096];
  std::string out;
  long rows = 0;
  for (;;) {
%(read)s
%(set)s
    top->eval();
%(print)s
    out += '\n';
    ++rows;
    if (out.size() > (1u << 20)) { fwrite(out.data(), 1, out.size(), stdout); out.clear(); }
  }
  fwrite(out.data(), 1, out.size(), stdout);
  printf("END %%ld\n", rows);
  top->final();
  return 0;
}
"""


def ccode_ident(name):
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        raise Reject(f"the port name `{name}` is not a plain identifier (the Verilator harness "
                     "reads ports by their C++ member names)")
    return name


def harness_cpp(ins, outs, template=HARNESS, **extra):
    """The C++ main of one run: read every vector (hex words per input, in the
    order of `ins`), `eval()` the model, print one row of binary strings per
    outputs in `outs` order, then `END <rows>`. A malformed or short vector is
    exit status 3 (fail closed)."""
    read, setl, prl = [], [], []
    for k, (n, w) in enumerate(ins):
        n = ccode_ident(n)
        nw = max(1, (w + 31) // 32)
        read.append(f"    uint32_t w_{n}[{nw}];\n"
                    f"    {{ const int r = fscanf(fp, \"%4095s\", tok);\n"
                    + ("      if (r == EOF) break;\n" if k == 0 else "")
                    + f"      if (r != 1 || !parse_hex(tok, w_{n}, {nw}, {w})) {{ "
                    f"fprintf(stderr, \"bad vector token for {n}\\n\"); return 3; }} }}")
        ty = f"std::remove_reference_t<decltype(top->{n})>"
        if w <= 32:
            setl.append(f"    top->{n} = static_cast<{ty}>(w_{n}[0]);")
        elif w <= 64:
            setl.append(f"    top->{n} = static_cast<{ty}>(((uint64_t)w_{n}[1] << 32) | w_{n}[0]);")
        else:
            setl.append(f"    for (int i = 0; i < {nw}; ++i) top->{n}[i] = w_{n}[i];")
    for k, (n, w) in enumerate(outs):
        n = ccode_ident(n)
        sep = "    out += ' ';\n" if k else ""
        if w <= 64:
            prl.append(f"{sep}    {{ const uint64_t v = (uint64_t)top->{n}; "
                       f"const uint32_t ow[2] = {{(uint32_t)v, (uint32_t)(v >> 32)}}; "
                       f"put_bits(out, ow, {w}); }}")
        else:
            prl.append(f"{sep}    put_bits(out, &top->{n}[0], {w});")
    return template % {"prefix": VL_PREFIX, "read": "\n".join(read), "set": "\n".join(setl),
                       "print": "\n".join(prl), **extra}


def run_group(cmd, timeout, spec=None, label=None, **kw):
    """`subprocess.run(capture_output, text)` that, on a timeout, kills the whole
    process group (make's compilers, Verilator's perl) and not just the child,
    so a stuck build leaves nothing running. Raises subprocess.TimeoutExpired.
    With an active sandbox and a `spec` (check/sandbox) the command runs under it
    and under the supervisor's limits (memory, output, file size)."""
    if spec is not None and sandbox.policy().active:
        return sandbox.run(cmd, spec, env=kw.get("env"), cwd=kw.get("cwd"), timeout=timeout, kind="tool",
                           label=label)
    kw.setdefault("env", sandbox.scrubbed_env())     # never the checker's own environment
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         start_new_session=True, **kw)
    try:
        out, err = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        p.communicate()
        raise
    return subprocess.CompletedProcess(cmd, p.returncode, out, err)


def error_lines(text, limit=1500):
    """The diagnostics of a build log: the lines that say error, or its tail."""
    hits = [ln for ln in text.splitlines() if re.search(r"error|not found|no such|fatal", ln,
                                                        re.IGNORECASE)]
    return ("\n".join(hits) if hits else text.strip())[-limit:]


def vl_env():
    """Verilator's environment: no compiler cache, a fixed locale."""
    env = sandbox.scrubbed_env()
    env["OBJCACHE"] = ""
    env["LC_ALL"] = "C"
    return env


def vl_build(srcs, top, params, ins, outs, work, tag, timeout, rtl=False, harness=None,
             xflags=VL_X_FLAGS):
    """Compile `srcs` (the netlist + cell models, or the RTL) with the harness
    for `ins`/`outs` into one executable, in two steps. VERILATE
    (`verilator --cc --exe`: parse, lint, translate to C++): a failure is
    about the design, so it comes back as (None, seconds, error text) and the
    caller rejects. COMPILE (`make`: clang on Verilator's own output and the
    generated harness): a failure there says the toolchain is broken or out of
    resources, not that the design is wrong, so it raises InfraError.
    Returns (exe, seconds, None) on success."""
    vl = verilator_info()[0]
    cxx = cxx_path()
    make = tool("make")
    d = os.path.join(work, f"{tag}_vl")
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(d)
    tb = os.path.join(d, "harness.cpp")
    with open(tb, "w") as fh:
        fh.write(harness_cpp(ins, outs) if harness is None else harness)
    obj = os.path.join(d, "obj")
    warn = list(RTL_FLAGS) if rtl else ["-Wall"] + [f"-Wno-{w}" for w in NETLIST_WNO]
    cmd = ([vl, "--cc", "--exe", "--prefix", VL_PREFIX, "--top-module", top, "--Mdir", obj,
            "--no-timing", "-CFLAGS", VL_CFLAGS] + list(xflags) + warn
           + [f"-G{k}={v}" for k, v in params.items()] + [tb]
           + [os.path.abspath(x) for x in srcs])
    env = vl_env()
    env["CXX"] = cxx
    vspec = mspec = None
    if sandbox.policy().active:        # the translator and the C++ build read the sources, write `d`
        env = sandbox.tool_env(d, {"OBJCACHE": "", "LC_ALL": "C", "CXX": cxx})
        reads = [os.path.abspath(x) for x in srcs] + [d]
        vspec = sandbox.tool_spec([vl], read=reads, write=[d], label="verilator")
        mspec = sandbox.tool_spec([make, cxx], read=[d], write=[d], label="make (C++ build)")
    t0 = time.time()
    try:
        c = run_group(cmd, timeout, spec=vspec, label="verilator", env=env, cwd=d)
        if c.returncode != 0:
            # the first diagnostics are the informative ones
            return None, time.time() - t0, (f"verilator rejected it (exit {c.returncode}): "
                                            + (c.stderr + c.stdout).strip()[:1500])
        m = run_group([make, "-C", obj, "-f", f"{VL_PREFIX}.mk", "-j", VL_JOBS, VL_PREFIX],
                      timeout, spec=mspec, label="make (C++ build)", env=env)
    except subprocess.TimeoutExpired:
        raise InfraError(f"building the Verilator model did not finish within {timeout:.0f}s")
    el = time.time() - t0
    exe = os.path.join(obj, VL_PREFIX)
    if m.returncode != 0 or not os.path.isfile(exe):
        raise InfraError("the C++ build of the Verilator model failed (toolchain, not design): "
                         + error_lines(m.stderr + m.stdout))
    return exe, el, None


# The dynamic loader's own words when a program cannot start because a shared library is missing: glibc's ld.so
# ("<prog>: error while loading shared libraries: libatomic.so.1: cannot open shared object file", exit 127) and
# macOS's dyld ("dyld[pid]: Library not loaded: @rpath/libX.dylib", then abort). The compiled model printed nothing:
# its main() never ran, so the cause is the toolchain the model was built with, never the design.
LOADER_FAILURE = re.compile(r"error while loading shared libraries: ([^:\s]+)|Library not loaded: (\S+)")


def loader_failure(r):
    """Raise InfraError when the run `r` of a compiled model died in the dynamic loader (LOADER_FAILURE, nonzero
    exit, nothing on stdout), naming the library; else nothing."""
    m = LOADER_FAILURE.search(r.stderr or "")
    if r.returncode == 0 or (r.stdout or "").strip() or not m:
        return
    where = (" inside the sandbox, which mounts the system library trees and the model, nothing else"
             if sandbox.policy().active else "")
    raise InfraError(f"the compiled Verilator model could not start (exit {r.returncode}): the dynamic loader did not "
                     f"find `{m.group(1) or m.group(2)}`{where}. The C++ toolchain links a runtime library the model "
                     "cannot load: the toolchain, not the design (README.md, \"Checking\")")


def vl_run(exe, ins, outs, vecs, work, tag, timeout):
    """Run a compiled model on `vecs`: (rows [{name: binary string}], seconds,
    None) or (None, seconds, error text). Fails closed on a nonzero exit, a
    missing end marker or a row count / row shape that is not exactly the
    vectors'."""
    vp = os.path.join(work, f"{tag}.hex")
    with open(vp, "w") as fh:
        for v in vecs:
            fh.write(" ".join(f"{v[n]:x}" for n, _ in ins) + "\n")
    t0 = time.time()
    try:
        # the compiled model is code made from the submission (a `$system` in the RTL would run in it):
        # it executes itself, reads the vector file and nothing else, starts nothing, writes nothing
        r = run_group([exe, vp], timeout, spec=sandbox.exec_spec(exe, read=[vp], label="model"), label="model",
                      env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"} if sandbox.policy().active else None)
    except subprocess.TimeoutExpired:
        return None, time.time() - t0, f"the Verilator model did not finish within {timeout:.0f}s"
    el = time.time() - t0
    loader_failure(r)
    lines = r.stdout.splitlines()
    end = lines[-1].split() if lines else []
    rows = [ln.split() for ln in lines[:-1]]
    widths = [w for _, w in outs]
    if (r.returncode != 0 or end != ["END", str(len(vecs))] or len(rows) != len(vecs)
            or any(len(x) != len(outs) or any(set(t) - set("01") or len(t) != w
                                              for t, w in zip(x, widths)) for x in rows)):
        return None, el, (f"the Verilator model printed {len(rows)} rows for {len(vecs)} vectors "
                          f"(exit {r.returncode}, end marker {' '.join(end) or 'missing'}): "
                          f"{(r.stdout[-300:] + r.stderr).strip()[-800:]}")
    return [dict(zip([n for n, _ in outs], x)) for x in rows], el, None


# ---------------------------------------------------------------- the check

def has_xz(s):
    return bool(re.search(r"[xzXZ]", s))


# ---------------------------------------------------------------- the advisory oracle

EXAMPLES_MAX = 3      # mismatching vectors listed in the `functional` object


def load_oracle(task_dir, task):
    """The task's advisory oracle: `(fn, None)`; `(None, None)` when the task
    names none (or `task_dir` is unknown); `(None, why)` when it names one that
    cannot be loaded. It is loaded when the check starts, before any submission
    code runs, and a failure never raises: the check is advisory."""
    name = task.get("oracle")
    if not name or not task_dir:
        return None, None
    path = os.path.realpath(os.path.join(task_dir, name))
    tdir = os.path.realpath(task_dir)
    if os.path.commonpath([path, tdir]) != tdir or not os.path.isfile(path):
        return None, f"the task's oracle {name!r} is not a file of the task directory"
    try:
        import importlib.util
        spec = importlib.util.spec_from_file_location(f"svgolf_oracle_{task['name']}", path)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        fn = getattr(mod, "oracle", None)
    except Exception as e:     # noqa: BLE001  (advisory: reported, never raised)
        return None, f"the task's oracle {name!r} does not load: {type(e).__name__}: {str(e)[:150]}"
    if task.get("kind") in CLOCKED_KINDS:
        fn = mod       # the clocked check's evaluator: the module (`clocked_oracle`)
    if not callable(fn) and fn is not mod:
        return None, f"the task's oracle {name!r} defines no function `oracle(params, inputs)`"
    return fn, None


def clocked_oracle(oracle, kind=None):
    """The clocked check's evaluator from `load_oracle`'s pair: BINDING (check (ii)), so a missing
    one, or one without `txns` and `good` (tx-family, stream-family) / `expect` (seq-family) /
    `segments` and `violations` (react-family), is an infrastructure error, never a pass."""
    mod, why = oracle if oracle else (None, "the task names no oracle.py")
    need = ("segments", "violations") if kind == "react-family" else ("txns",)
    if mod is None or not all(callable(getattr(mod, f, None)) for f in need):
        raise InfraError(f"the clocked post-synthesis check needs the task's oracle.py with "
                         f"{' and '.join(f'`{f}`' for f in need)}: {why or 'it has none'}")
    return mod


def functional_check(oracle, params, point_s, ins, outs, vecs, lrows):
    """The `functional` object (module docstring) of ls-sv's `lrows` on `vecs`
    against `oracle` = `load_oracle`'s pair. Pure; never raises. Only a vector
    on which ls-sv gave known values (σ_src) AND the oracle answered with
    exactly the output ports, each an int below its width's range, is checked;
    every other vector is `unchecked`, never a mismatch."""
    fn, why = oracle
    widths = dict(outs)
    checked = mism = unchecked = 0
    examples = []
    note = why
    if fn is None:
        return {"checked": 0, "mismatches": 0, "examples": [], "unchecked": len(vecs),
                "note": why or "no oracle"}
    for v, lr in zip(vecs, lrows):
        src = lr[0] if isinstance(lr, tuple) and lr and isinstance(lr[0], dict) else None
        if src is None or any(o not in src or has_xz(src[o]) for o in widths):
            unchecked += 1     # an ls-sv error or x/z: the stage's own verdicts report it
            continue
        try:
            exp = fn(dict(params), dict(v))
            if not isinstance(exp, dict) or set(exp) != set(widths):
                raise ValueError(f"returned {sorted(exp) if isinstance(exp, dict) else exp!r}, "
                                 f"expected the output ports {sorted(widths)}")
            for o, w in widths.items():
                if isinstance(exp[o], bool) or not isinstance(exp[o], int) \
                        or not 0 <= exp[o] < (1 << w):
                    raise ValueError(f"{o} = {exp[o]!r} is not an int below 2^{w}")
        except Exception as e:     # noqa: BLE001  (an oracle fault is "unchecked")
            unchecked += 1
            note = note or f"the oracle failed on a vector: {type(e).__name__}: {str(e)[:150]}"
            continue
        got = {o: int(src[o], 2) for o in widths}
        checked += 1
        if got != exp:
            mism += 1
            if len(examples) < EXAMPLES_MAX:
                examples.append({"point": point_s or "default",
                                 "inputs": {n: hex(v[n]) for n, _ in ins},
                                 "expected": {o: hex(exp[o]) for o, _ in outs},
                                 "got": {o: hex(got[o]) for o, _ in outs}})
    out = {"checked": checked, "mismatches": mism, "examples": examples}
    if unchecked:
        out["unchecked"] = unchecked
    if note:
        out["note"] = note
    return out


def functional_warning(functional):
    """The ONE warning line for a `functional` object with mismatches (else None)."""
    if not functional or not functional.get("mismatches"):
        return None
    e = functional["examples"][0]
    diff = [o for o in e["expected"] if e["expected"][o] != e["got"][o]]
    return ("functional: the design disagrees with the task's function on "
            f"{functional['mismatches']} of {functional['checked']} vectors; first: "
            + " ".join(f"{k}={v}" for k, v in e["inputs"].items())
            + " expected " + " ".join(f"{o}={e['expected'][o]}" for o in diff)
            + " got " + " ".join(f"{o}={e['got'][o]}" for o in diff)
            + " (an advisory check: the Lean proof is the authority, but a design that "
            "computes something else cannot have one)")


def verdict3(lssv, net, rtl):
    """Who agrees with whom, for the bug report."""
    if rtl is None:
        return "no third opinion"
    if lssv is None:
        return ("ls-sv gives no value; Verilator-RTL " + ("agrees" if rtl == net else "DISAGREES")
                + " with the netlist")
    if rtl == lssv and rtl != net:
        return "Verilator-RTL agrees with ls-sv: Yosys reads the design differently"
    if rtl == net and rtl != lssv:
        return "Verilator-RTL agrees with the netlist: ls-sv reads the design differently"
    if rtl == net == lssv:
        return "all three agree on the values (an x/z or schedule issue)"
    return "no two of ls-sv, the netlist and Verilator-RTL agree"


def run(task, canon_sv, envl, netlist, sres, work, point=None, third_all=False, rng_salt=None,
        random_count=None, oracle=None, mode=None):
    """The postsynth check of the design `canon_sv` (the canonical text) whose
    envelope is `envl` and whose scored netlist (score result `sres`) is
    `netlist`, at `point` (default: the task's scoring point). Returns the
    record; raises Reject (with the record in `.info["record"]`) or InfraError.
    `oracle` is `load_oracle`'s pair: with one, the record gets the advisory
    `functional` object (module docstring); it never changes the verdict.
    `mode` is "light" or "full" (None: `resolve_mode`'s default); the record
    says which ran (`mode`)."""
    t_start = time.time()
    cfg = config(task)
    mode = resolve_mode(mode)
    top = task["top"]
    params = ({k: int(v) for k, v in task["scoring"]["params"].items()} if point is None
              else dict(point))
    point_s = envelope.point_str(params)
    salt = os.environ.get("SVGOLF_POSTSYNTH_SALT", "") if rng_salt is None else rng_salt
    with open(canon_sv, "rb") as fh:
        canon = fh.read()
    rec = {"point": point_s or "default", "envelope_sha256": sha256_file(envl),
           "netlist_sha256": sha256_file(netlist), "sveval_sha256": sha256_file(SVEVAL)
           if os.path.isfile(SVEVAL) else None, "salted": bool(salt), "fuel": cfg["fuel"],
           "mode": mode}
    deadline = t_start + float(cfg["time_limit_s"])
    try:
        _, rec["verilator"], _ = verilator_info()
        cxx_path(), tool("make")
        t0 = time.time()
        design, drivers = reread_check(netlist, top, sres, work)
        unread, readers = unknown_bits(design, top)
        xlit = unknown_message(unread, readers, unknown_names(sres) if readers else None,
                               read_unknown(drivers, top) if readers else None)
        if xlit:
            rec["netlist_unknown_constant"] = xlit
        elif unread:
            rec["netlist_unread_unknown"] = unread
            print(unread_note(unread), file=sys.stderr, flush=True)
        rec["t_reread_s"] = round(time.time() - t0, 2)
        nports = netlist_ports(design, top)
        ins = sorted((n, w) for d, n, w in nports if d == "input")
        outs = sorted((n, w) for d, n, w in nports if d == "output")
        if not ins or not outs:
            raise Reject(f"the netlist has no {'inputs' if not ins else 'outputs'}: {nports}")
        seed = hashlib.sha256(b"\0".join([salt.encode(), task["name"].encode(),
                                          point_s.encode(), canon])).hexdigest()
        rec["seed"] = seed
        rng = random.Random(seed)
        fixed, nfixed = fixed_vectors(ins, cfg["corners"])
        t0 = time.time()
        harvest, nh = harvest_vectors(canon_sv, top, params, ins, work, rng, cfg["harvest_pairs"])
        rec["t_harvest_s"] = round(time.time() - t0, 2)
        k = cfg["random"] if random_count is None else random_count
        rand = [{n: rng.getrandbits(w) for n, w in ins} for _ in range(k)]
        full_vecs = dedup(ins, fixed + harvest + rand)
        rec["outputs"] = [n for n, _ in outs]
        if mode == "full":
            vecs = full_vecs
            rec.update(vectors=len(vecs), fixed=nfixed, task_corners=len(fixed) - nfixed,
                       harvested_constants=nh, harvest_vectors=len(harvest), random=k)
        else:
            # a subset of the full set (same seed, same stream): `light_select`
            lv, counts = light_select(fixed, nfixed, harvest, nh, rand, int(cfg["light_vectors"]))
            vecs = dedup(ins, lv)
            rec.update(vectors=len(vecs), harvested_constants=nh, light_vectors=int(
                cfg["light_vectors"]), **counts)
        rec["full_vectors"] = len(full_vecs)
        if mode == "light":
            rec["full_counts"] = {"fixed": nfixed, "task_corners": len(fixed) - nfixed,
                                  "harvest_vectors": len(harvest), "random": k}
        # The model of the scored netlist is built while ls-sv evaluates (the
        # build is a few seconds and does not depend on ls-sv's answer; the
        # `finally` joins it, so nothing keeps writing into `work` after a
        # rejection). The verdicts keep their order: ls-sv's come first.
        pool = concurrent.futures.ThreadPoolExecutor(max_workers=1)
        try:
            build = pool.submit(vl_build, [netlist, simcells()], top, {}, ins, outs, work,
                                "netlist", max(120.0, deadline - time.time()))
            lports, lrows, design, timing, el = lssv_eval(envl, point_s, ins, vecs, cfg["fuel"],
                                                          work, deadline)
            rec.update(lssv_design=design, lssv_timing=timing, t_lssv_s=round(el, 2),
                       lssv_ms_per_vector=round(1000 * el / len(vecs), 3))
            errs = [r[1] for r in lrows if r[0] == "ERROR"]
            if errs and len(errs) == len(lrows) and all(e.startswith("UNSUPPORTED") for e in errs):
                rec["unsupported_runs"] = len(lrows)
                raise Reject("ls-sv does not support this design: every one of the "
                             f"{len(lrows)} runs is UNSUPPORTED ({errs[0][:300]}). This is an "
                             "ls-sv limit, not a disagreement: the design uses a construct ls-sv "
                             "cannot evaluate (the `design` stage loads such a design with an "
                             "unsupported node, and no proof about it can hold). Rewrite it "
                             "without the construct, or add the construct to ls-sv by PR "
                             "(README.md, \"Rules\").")
            if lports != nports:
                raise Reject("the ports differ: ls-sv has " + str(sorted(lports - nports))
                             + " where the netlist has " + str(sorted(nports - lports))
                             + " (direction, name, width)")
            if oracle is not None and (oracle[0] is not None or oracle[1] is not None):
                try:
                    rec["functional"] = functional_check(oracle, params, point_s, ins, outs, vecs,
                                                         lrows)
                except Exception as e:     # noqa: BLE001  (advisory: a fault here is no verdict)
                    rec["functional"] = {"checked": 0, "mismatches": 0, "examples": [],
                                         "unchecked": len(vecs),
                                         "note": f"internal error: {type(e).__name__}: {e}"[:200]}
            exe, el, err = build.result()
        finally:
            pool.shutdown(wait=True)
        rec["t_netlist_build_s"] = round(el, 2)
        if exe is None:
            raise Reject(f"the scored netlist does not compile: {err}")
        nrows, el, err = vl_run(exe, ins, outs, vecs, work, "netlist",
                                max(60.0, deadline - time.time()))
        rec["t_netlist_run_s"] = round(el, 3)
        if nrows is None:
            raise Reject(f"the scored netlist does not simulate: {err}")
        bad = []
        for i, (v, lr, nr) in enumerate(zip(vecs, lrows, nrows)):
            why = []
            if lr[0] == "ERROR":
                why.append(f"ls-sv: {lr[1]}")
            else:
                src, rev = lr
                if src != rev:
                    why.append("ls-sv: σ_src and σ_rev disagree")
                for o, _ in outs:
                    if has_xz(src.get(o, "x")):
                        why.append(f"ls-sv: {o} has x/z")
                    if src.get(o) != nr[o]:
                        why.append(f"{o}: ls-sv != netlist")
            if xlit:     # the 2-state netlist shows 0/1 where something reads an x
                why.append(xlit)
            if why:
                bad.append((i, v, lr, nr, why))
        rec["mismatches"] = len(bad)
        rtl_model = {}

        def rtl_eval(vs, tag, timeout):
            """The RTL third opinion on `vs`: (rows or None, error). The model
            is built once per run and reused."""
            if "exe" not in rtl_model:
                t1 = time.time()
                try:
                    exe, _, e = vl_build([canon_sv], top, params, ins, outs, work, "rtl",
                                         timeout, rtl=True)
                except Reject as r:
                    exe, e = None, r.msg
                rec["t_rtl_build_s"] = round(time.time() - t1, 2)
                rtl_model.update(exe=exe, err=e)
            if rtl_model["exe"] is None:
                return None, rtl_model["err"]
            rows, _, e = vl_run(rtl_model["exe"], ins, outs, vs, work, tag, timeout)
            return rows, e

        if third_all:
            t0 = time.time()
            rtl_all, err = rtl_eval(vecs, "rtl_all", max(60.0, deadline - time.time()))
            rec["t_rtl_s"] = round(time.time() - t0, 2)
            if rtl_all is None:
                rec["verilator_rtl"] = err
            else:
                rec["lssv_vs_verilator_rtl"] = sum(1 for lr, rr in zip(lrows, rtl_all)
                                                   if lr[0] == "ERROR" or lr[0] != rr)
                rec["netlist_vs_verilator_rtl"] = sum(1 for nr, rr in zip(nrows, rtl_all)
                                                      if nr != rr)
        if bad:
            report = bad[:REPORT_MAX]
            rtl, err = rtl_eval([b[1] for b in report], "rtl", 120.0)
            if rtl is None:
                rec["verilator_rtl"] = f"third opinion unavailable: {err}"
            rec["report"] = []
            for j, (i, v, lr, nr, why) in enumerate(report):
                ls = lr[0] if lr[0] != "ERROR" else None
                rec["report"].append({
                    "vector": i, "inputs": {n: hex(v[n]) for n, _ in ins}, "why": why,
                    "lssv_src": ls, "lssv_rev": lr[1] if ls is not None else None,
                    "lssv_error": lr[1] if ls is None else None, "netlist": nr,
                    "verilator_rtl": rtl[j] if rtl else None,
                    "verdict": verdict3(ls, nr, rtl[j] if rtl else None)})
            raise Reject(f"{len(bad)} of {len(vecs)} vectors: ls-sv and the scored netlist "
                         "disagree\n" + bug_report(rec, task, point_s))
    except Reject as r:
        rec["seconds"] = round(time.time() - t_start, 2)
        r.info["record"] = rec
        raise
    rec["seconds"] = round(time.time() - t_start, 2)
    return rec


# ---------------------------------------------------------------- the clocked check
#
# For the CLOCKED kinds (`run_clocked`). Per seed (S = 8 per point, F5), the netlist starts
# from a concrete power-up state (Verilator `--x-initial unique`: seed 0 all zeros, `randReset(0)`; every
# other seed random, `randReset(2)`, `randSeed` from the seed's salted draw: `seed_draw`), reset is asserted for
# `reset_cycles` entries (C1; the other inputs random), then the task's own generator (oracle.py
# `txns(params, seed, count, rng)`, `rng` the seed's salted source) drives it: for tx-family each transaction's `gap` free entries, its
# start entry, then its operands held until the netlist's `done` shows 1, so a gap of 0 is C2's
# back-to-back start (or until `n` cycles have passed: late, the run stops), and `tail` idle
# entries after the last; for stream-family each transaction's `gap` free entries, its start entry,
# its `count` values on `in_data` with `in_valid` = 1, then free entries until the netlist has shown
# the `count`-th `out_valid` = 1 since the start (StreamTask.Idle: the gap counts from the entry after
# that snapshot; at most `n` cycles after the start, then late), `in_valid` = 0 outside the values;
# for seq-family the generator's entries verbatim. One entry is one clock
# period: the inputs with the clock at 0, then the rising edge; the row is the snapshot after it
# (ls-sv's protocol). The realized stimulus is then ONE `svgolf-eval --trace` run of ls-sv from a
# concrete power-up state (txtask-v2 rule 2, 2026-11-05: an unreset register is an unknown 0/1 value,
# not ls-sv's x start, whose x-optimism is a simulator's resolution): seed 0 from all zeros, the
# netlist's own start; every other seed from ls-sv's seeded random power-up (`--start seed:<n>`),
# which need not be the netlist's (its flops are not named after the registers): a design whose
# claims hold from every power-up and FIX the cared outputs shows the same cared outputs from both
# (seq-family's claim fixes every output, so seq-family compares bit for bit at every seed). A
# tx/stream design whose `done`/`out_valid` timing within the latency depends on an unreset register
# can be correct and differ between two power-ups (design/soundness/TXTASK-V2-REVIEW.md section 12.2,
# L5), so since 2026-11-08 the transaction kinds compare bit for bit only from the SAME state, as the
# reactive check below does: seed 0 when `zero_starts_agree`; from different power-ups ls-sv's run is
# held to the statement's claims on its own (`lssv_claims`, L5 below).
# Before 2026-11-05 ls-sv ran from `initState2` (declaration initializers, all else x), which
# rejected an x-pessimistic design that is correct from every concrete start (`y = u ^ u`, u
# unreset: x there, 0 in every run).
# Binding, either failing rejects: (i) on the CARED outputs of every cycle the
# netlist equals ls-sv (under σ_src, which must equal σ_rev), and ls-sv's value is known (an x or z
# there would be some 0/1 in the 2-state netlist), where the two start from the same state (tx/stream:
# from different states, ls-sv's run meets the guarantee up to its rely horizon, `lssv_claims`); (ii) the netlist's claimed payload is the task's
# evaluator's, oracle.py `good(params, txn, result)` (tx-family; stream-family with result
# `{"out": the values emitted from the start to the next}`) / `expect(params, entries)` (seq-family:
# the outputs per entry). Cared (C4, C5): tx-family `done` at every cycle from the release, 0 before the first
# start (since 2026-11-09), and the payload from a transaction's first `done` to the next start, where `done` must
# stay 1 (the hold);
# stream-family `out_valid` at every cycle from the release, 0 before the first start, and
# `out_data` where `out_valid` = 1; seq-family every output from the first reset entry (SeqTask's
# claim). The latency (C3): `done` shows 1 / every `out_valid` = 1 is at most `n` cycles after the
# start entry's snapshot (cycle 0).
VL_X_CLOCKED = ("--x-assign", "0", "--x-initial", "unique")
CLOCKED_HARNESS = HARNESS.split("int main(")[0] + r"""// THE CLOCKED HARNESS: argv VECTORS SEED CAP RESET (RESET: Verilator's randReset policy, 0 = all
// zeros, 2 = random from SEED).
// A line is a kind, then one hex token per input but the clock: `E` one entry, `S` one entry that
// starts a transaction (its row is cycle 0), `H` the hold: unless the last row shows done = 1,
// entries of these values until one does, at most CAP rows after the start (then `END <rows> LATE`),
// `W` one entry unless the last row shows done = 1 (a stream's wait, each with its own values).
// A row is the line number, then the outputs after the cycle.
int main(int argc, char** argv) {
  if (argc != 5) { fprintf(stderr, "usage: harness VECTORS SEED CAP RESET\n"); return 2; }
  FILE* fp = fopen(argv[1], "r");
  if (!fp) { fprintf(stderr, "cannot open %%s\n", argv[1]); return 2; }
  const std::unique_ptr<VerilatedContext> ctx{new VerilatedContext};
  ctx->randReset(atoi(argv[4]));
  ctx->randSeed(atoi(argv[2]));
  const long cap = atol(argv[3]);
  const std::unique_ptr<%(prefix)s> top{new %(prefix)s{ctx.get(), "TOP"}};
  char tok[4096], kind[8];
  std::string out;
  long rows = 0, line = -1, since = 0;
  bool done = false, late = false;
  while (!late && fscanf(fp, "%%7s", kind) == 1) {
    ++line;
%(read)s
    if (kind[0] == 'W' && done) continue;
    const bool hold = kind[0] == 'H';
    for (bool first = true; hold ? !done : first; first = false) {
      if (hold && since >= cap) { late = true; break; }
%(set)s
      top->%(clk)s = 0; top->eval();
      top->%(clk)s = 1; top->eval();
      done = %(done)s;
      since = kind[0] == 'S' ? 0 : since + 1;
      out += std::to_string(line) + ' ';
%(print)s
      out += '\n';
      ++rows;
    }
  }
  fwrite(out.data(), 1, out.size(), stdout);
  printf("END %%ld%%s\n", rows, late ? " LATE" : "");
  top->final();
  return 0;
}
"""


def clocked_plan(task, mod, point, seed, cfg, dins, rng):
    """One seed's stimulus lines [(kind, {input: value})] and the generator's items."""
    rp, lvl = task["reset"]["port"], int(task["reset"].get("level", 1))
    def rnd(**kv):
        return {**{n: rng.getrandbits(w) for n, w in dins}, **kv}
    lines = [("E", rnd(**{rp: lvl})) for _ in range(cfg["reset_cycles"])]
    items = mod.txns(dict(point), seed, cfg["txns"], rng=rng)   # the salted source (F5); `seed` picks the corner case
    if task["kind"] == "seq-family":
        return lines + [("E", rnd(**e)) for e in items], items
    proto = task["protocol"]
    if task["kind"] == "stream-family":
        st, iv, dt, n = proto["start"], proto["in_valid"], proto["in_data"], int(point[proto["count"]])
        for t in items:
            fr, g = t["free"], t["gap"]
            if len(t["xs"]) != n or not fr:
                raise InfraError(f"oracle.py `txns`: a transaction has {len(t['xs'])} values (the count is {n}) "
                                 f"and {len(fr)} free values")
            def ent(i, **kv):          # the free values in order and cyclically, in_valid 0
                return rnd(**{rp: 1 - lvl, st: 0, iv: 0, dt: fr[i % len(fr)], **kv})
            lines += [("E", ent(i)) for i in range(g)] + [("S", ent(g, **{st: 1}))]
            lines += [("E", ent(0, **{iv: 1, dt: x})) for x in t["xs"]]
            lines += [("W", ent(i)) for i in range(g + 1, len(fr))] + [("H", ent(len(fr)))]
        return lines + [("E", rnd(**{rp: 1 - lvl, st: 0, iv: 0})) for _ in range(cfg["tail"])], items
    for t in items:
        idle = {rp: 1 - lvl, proto["start"]: 0}
        x = {o: t[o] for o in proto["operands"]}
        lines += [("E", rnd(**f, **idle)) for f in t["free"]]
        lines += [("S", rnd(**x, **{**idle, proto["start"]: 1})), ("H", rnd(**x, **idle))]
    return lines + [("E", rnd(**{rp: 1 - lvl, proto["start"]: 0})) for _ in range(cfg["tail"])], items


# THE SALTED RANDOMNESS OF A CLOCKED RUN (F5, decided 2026-11-07; S = 8 seeds per point, CLOCKED_DEFAULTS and
# REACT_DEFAULTS). Every clocked kind derives everything random in one seed's run from h = sha256($SVGOLF_POSTSYNTH_SALT,
# task, point, seed) and records it (`seed_draw`, the seed's record): the stimulus generator's source (the free input
# bits, oracle.py's `txns` or `segments`), Verilator's `randSeed` (the netlist's random power-up) and ls-sv's
# power-up `seed:<k>`. With the default empty salt anyone reproduces a run; a competition sets a secret one, and
# neither the stimulus nor either power-up can be predicted. The design is not in h. Seed 0 starts both sides from
# all zeros (no draw: `start_of`); seed s > 0 from a random power-up of each.
SEED_MAX_VL = 2 ** 31 - 1      # Verilator's `randSeed` is an int (the harness's `atoi`); 0 would be time-seeded


def seed_draw(task, point_s, seed, salt=None):
    """One seed's randomness (above): {`rng` (random.Random(int(h, 16))), `seed_sha256` (h), `salted` (a salt was
    set), `vl_seed` (1 .. SEED_MAX_VL: sha256(h + "/verilator")), `lssv_k` (64 bits: sha256(h + "/lssv"))}."""
    salt = os.environ.get("SVGOLF_POSTSYNTH_SALT", "") if salt is None else salt
    h = hashlib.sha256(b"\0".join([salt.encode(), task["name"].encode(), point_s.encode(),
                                   str(seed).encode()])).hexdigest()
    sub = lambda tag: int(hashlib.sha256(f"{h}/{tag}".encode()).hexdigest(), 16)  # noqa: E731
    return {"rng": random.Random(int(h, 16)), "seed_sha256": h, "salted": bool(salt),
            "vl_seed": 1 + sub("verilator") % SEED_MAX_VL, "lssv_k": sub("lssv") % 2 ** 64}


def start_of(seed, draw):
    """The power-up of `seed`'s run: (Verilator's randReset policy, svgolf-eval's `--start`). Seed 0 starts both
    from all zeros; every other seed each from its own random power-up, ls-sv's `seed:<k>` from the seed's draw
    (`seed_draw`; the netlist's from its `vl_seed`)."""
    return (0, "zeros") if seed == 0 else (2, f"seed:{draw['lssv_k']}")


def vl_run_clocked(exe, dins, outs, lines, seed, draw, cap, work, timeout):
    """The clocked model on `lines`, from `seed`'s power-up (`start_of`, Verilator's `randSeed` the draw's
    `vl_seed`): ([(line, {output: bits})], late, seconds, None) or (None, None, seconds, error). Fails closed like
    `vl_run`."""
    vp = os.path.join(work, f"clocked_{seed}.hex")
    with open(vp, "w") as fh:
        for k, v in lines:
            fh.write(k + " " + " ".join(f"{v[n]:x}" for n, _ in dins) + "\n")
    t0 = time.time()
    try:
        r = run_group([exe, vp, str(draw["vl_seed"]), str(cap), str(start_of(seed, draw)[0])], timeout,
                      spec=sandbox.exec_spec(exe, read=[vp], label="model"), label="model",
                      env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"} if sandbox.policy().active else None)
    except subprocess.TimeoutExpired:
        return None, None, time.time() - t0, f"the Verilator model did not finish within {timeout:.0f}s"
    loader_failure(r)
    rows = [ln.split() for ln in r.stdout.splitlines()]
    end = rows.pop() if rows else []
    ok = (r.returncode == 0 and end[:2] == ["END", str(len(rows))] and end[2:] in ([], ["LATE"])
          and all(len(x) == len(outs) + 1 and x[0].isdigit() and int(x[0]) < len(lines)
                  and all(len(t) == w and not set(t) - set("01") for t, (_, w) in zip(x[1:], outs))
                  for x in rows))
    if not ok:
        return None, None, time.time() - t0, (f"the clocked Verilator model printed malformed rows (exit "
                                              f"{r.returncode}): {(r.stdout[-300:] + r.stderr).strip()[-800:]}")
    return ([(int(x[0]), dict(zip([n for n, _ in outs], x[1:]))) for x in rows], end[2:] == ["LATE"],
            time.time() - t0, None)


# ---------------------------------------------------------------- THE REACTIVE CHECK
#
# For `react-family` (a ReactTask statement, SvGolf/TaskReact.lean: no transactions, a safety monitor and
# bounded response over the whole trace). Per seed, the netlist starts from a power-up state (seed 0 all
# zeros, every other seed random, as the transaction kinds: `start_of`), then the task's oracle.py
# `segments(params, rng, count, long)` drives it: each segment is ONE reset entry (the
# first segment: `reset_cycles` of them) and then its entries with the reset deasserted; the last segment
# is `long` entries long, so a design that changes after many cycles (a counter, a time bomb) is driven past
# that point. The generator's random source is seeded by sha256($SVGOLF_POSTSYNTH_SALT, task, point, seed):
# with the default empty salt anyone reproduces a run; a competition sets a secret one, and the stimulus is
# unpredictable. The design is not in the seed, so no edit of the text chooses its own stimulus. The
# realized stimulus is then ONE `svgolf-eval --trace` run of ls-sv from a power-up state (the statement's
# runs since 2026-11-06, txtask-v2's rule 2: seed 0 from all zeros, the netlist's own start; every other
# seed from ls-sv's seeded random power-up, which need not be the netlist's). A reactive guarantee admits
# several outputs (any legal grant), so a design correct from every power-up may show different outputs
# from two different power-ups (an arbiter whose mask is not reset: txtask-v2 review section 12, F4):
# the netlist is compared with ls-sv bit for bit only where the two start from the SAME state
# (`zero_starts_agree`: seed 0, when the pinned flow replaced no register and no array lane by the
# constant 1). Binding, any failure rejects:
#   (i)   every output at every snapshot from the last entry of the first reset on: ls-sv's value is
#         known and σ_src equals σ_rev; from the same state the netlist equals ls-sv; from different
#         states ls-sv's outputs meet the guarantee (the evaluator of (ii), on ls-sv's run);
#   (ii)  on every segment, the NETLIST's outputs meet the guarantee, oracle.py `violations(params,
#         reset snapshot, entries, snapshots)` (for the arbiter: G0 to G4, the bound K = N - 1);
#   (iii) Moore: the harness also samples every output BEFORE each rising edge, with the entry's inputs
#         applied to the previous snapshot's state, and that sample must equal the previous snapshot: an
#         output that moves with the inputs between two edges has a combinational path from an input
#         (the statement's `MooreOut`; a snapshot-only check cannot see it, the silicon does).
REACT_HARNESS = HARNESS.split("int main(")[0] + r"""// THE REACTIVE HARNESS: argv VECTORS SEED RESET (RESET: Verilator's randReset policy, 0 = all
// zeros, 2 = random from SEED).
// A line is `E`, then one hex token per input but the clock: one entry. A row is the line number, the
// outputs BEFORE the rising edge (the entry's inputs applied, the clock at 0, settled), `|`, then the
// outputs after the edge (the snapshot).
int main(int argc, char** argv) {
  if (argc != 4) { fprintf(stderr, "usage: harness VECTORS SEED RESET\n"); return 2; }
  FILE* fp = fopen(argv[1], "r");
  if (!fp) { fprintf(stderr, "cannot open %%s\n", argv[1]); return 2; }
  const std::unique_ptr<VerilatedContext> ctx{new VerilatedContext};
  ctx->randReset(atoi(argv[3]));
  ctx->randSeed(atoi(argv[2]));
  const std::unique_ptr<%(prefix)s> top{new %(prefix)s{ctx.get(), "TOP"}};
  char tok[4096], kind[8];
  std::string out;
  long rows = 0, line = -1;
  while (fscanf(fp, "%%7s", kind) == 1) {
    ++line;
    if (kind[0] != 'E') { fprintf(stderr, "bad line kind %%s\n", kind); return 3; }
%(read)s
%(set)s
    top->%(clk)s = 0; top->eval();
    out += std::to_string(line) + ' ';
%(print)s
    out += " |";
    top->%(clk)s = 1; top->eval();
    out += ' ';
%(print)s
    out += '\n';
    ++rows;
  }
  fwrite(out.data(), 1, out.size(), stdout);
  printf("END %%ld\n", rows);
  top->final();
  return 0;
}
"""


def react_rng(task, point_s, seed, salt=None):
    """The generator's random source for one seed and its h (`seed_draw`)."""
    d = seed_draw(task, point_s, seed, salt)
    return d["rng"], d["seed_sha256"]


def react_plan(task, mod, point, rng, cfg, dins):
    """One seed's stimulus lines [("E", {input: value})], the generator's segments and, per segment, the
    line index of its reset entry (the snapshot G0 reads) and of its first entry after the release."""
    rp, lvl = task["reset"]["port"], int(task["reset"].get("level", 1))
    data = [n for n, _ in dins if n != rp]
    segs = mod.segments(dict(point), rng, cfg["segments"], cfg["long"])
    lines, spans = [], []
    for k, sg in enumerate(segs):
        if set(sg["reset"]) != set(data) or any(set(e) != set(data) for e in sg["entries"]):
            raise InfraError(f"oracle.py `segments`: segment {k} ({sg.get('tag')}) does not drive exactly the data "
                             f"inputs {data}")
        lines += [("E", {**{n: rng.getrandbits(w) for n, w in dins if n != rp}, rp: lvl})
                  for _ in range(cfg["reset_cycles"] - 1 if k == 0 else 0)]
        lines.append(("E", {**sg["reset"], rp: lvl}))
        spans.append((len(lines) - 1, len(lines), len(lines) + len(sg["entries"])))
        lines += [("E", {**e, rp: 1 - lvl}) for e in sg["entries"]]
    return lines, segs, spans


def vl_run_react(exe, dins, outs, lines, seed, draw, work, timeout):
    """The reactive model on `lines`, from `seed`'s power-up (`start_of`, `randSeed` the draw's `vl_seed`):
    ([(pre {output: bits}, post {output: bits})], seconds, None) or (None, seconds, error). Fails closed like
    `vl_run`: one row per line, in order."""
    vp = os.path.join(work, f"react_{seed}.hex")
    with open(vp, "w") as fh:
        for k, v in lines:
            fh.write(k + " " + " ".join(f"{v[n]:x}" for n, _ in dins) + "\n")
    t0 = time.time()
    try:
        r = run_group([exe, vp, str(draw["vl_seed"]), str(start_of(seed, draw)[0])], timeout,
                      spec=sandbox.exec_spec(exe, read=[vp], label="model"), label="model",
                      env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"} if sandbox.policy().active else None)
    except subprocess.TimeoutExpired:
        return None, time.time() - t0, f"the Verilator model did not finish within {timeout:.0f}s"
    loader_failure(r)
    rows = [ln.split() for ln in r.stdout.splitlines()]
    end = rows.pop() if rows else []
    n = len(outs)
    ok = (r.returncode == 0 and end == ["END", str(len(lines))] and len(rows) == len(lines)
          and all(len(x) == 2 * n + 2 and x[0] == str(i) and x[n + 1] == "|"
                  and all(len(t) == w and not set(t) - set("01")
                          for t, (_, w) in zip(x[1:n + 1] + x[n + 2:], outs + outs))
                  for i, x in enumerate(rows)))
    if not ok:
        return None, time.time() - t0, (f"the reactive Verilator model printed malformed rows (exit "
                                        f"{r.returncode}): {(r.stdout[-300:] + r.stderr).strip()[-800:]}")
    names = [o for o, _ in outs]
    return ([(dict(zip(names, x[1:n + 1])), dict(zip(names, x[n + 2:]))) for x in rows],
            time.time() - t0, None)


def zero_starts_agree(sres):
    """Whether the netlist's all-zeros start (Verilator `randReset(0)`) is ls-sv's `zeros` power-up. Every flop the
    netlist keeps is a register bit, a merged copy of one or a bit equal to its lower neighbour (0 in both starts),
    and a register the flow replaced by the constant 0 is 0 in both; a register replaced by the constant 1 (opt_dff's
    "Setting constant 1-bit", a 1 once `never_loaded` has passed) or an array lane by the constant 1 (opt_mem's
    const-1 lane) reads 1 in the netlist where ls-sv's zero start reads 0 (txtask-v2 review section 11.2's KEPT
    rows); an undefined removal is refused at `score` before this check, and the clocked flow runs no fsm pass
    (`synth -nofsm`, decided 2026-11-06; an FSM re-encoding would be refused at `score` too, by the backstop)."""
    fr = (sres or {}).get("flop_removals") or {}
    return not fr.get("constant_one_or_x") and not fr.get("memory_constant_one")


def react_seed(task, mod, point, point_s, seed, cfg, envl, exe, nports, work, deadline, zeros_agree=True):
    """One seed of THE REACTIVE CHECK: (the record, the failures [(cycle, why)]). `zeros_agree`:
    `zero_starts_agree` of the scored record (seed 0 then starts both from the same state)."""
    clk, R = task["clock"], cfg["reset_cycles"]
    ins = sorted((n, w) for d, n, w in nports if d == "input")
    outs = sorted((n, w) for d, n, w in nports if d == "output")
    dins = [(n, w) for n, w in ins if n != clk]
    draw = seed_draw(task, point_s, seed)
    lines, segs, spans = react_plan(task, mod, point, draw["rng"], cfg, dins)
    rows, el, err = vl_run_react(exe, dins, outs, lines, seed, draw, work, max(60.0, deadline - time.time()))
    if rows is None:
        raise Reject(f"the scored netlist does not simulate: {err}")
    pre, net = [p for p, _ in rows], [q for _, q in rows]
    stim = [e for _, e in lines]
    start = start_of(seed, draw)
    rec = {"seed": seed, "seed_sha256": draw["seed_sha256"], "salted": draw["salted"],
           "reset_cycles": R, "cycles": len(stim), "segments": len(segs),
           "longest_segment": max(len(sg["entries"]) for sg in segs), "t_netlist_run_s": round(el, 3),
           "netlist_randreset": start[0], "netlist_randseed": draw["vl_seed"], "lssv_start": start[1]}
    same = seed == 0 and zeros_agree
    rec["compared"] = ("the netlist with ls-sv, bit for bit (the same all-zeros start)" if same else
                       "each run with the guarantee (the netlist and ls-sv start from different power-ups)")
    lports, lrows, _, _, el = lssv_eval(envl, point_s, ins, [{clk: 0, **e} for e in stim], cfg["fuel"],
                                        work, deadline, trace=True, start=start[1])
    rec["t_lssv_s"] = round(el, 2)
    if lports != nports:
        raise Reject(f"the ports differ: ls-sv has {sorted(lports)}, the netlist {sorted(nports)}")
    errs = [r[1] for r in lrows if r[0] == "ERROR"]
    if errs:
        raise Reject(f"ls-sv does not complete the run (seed {seed}): {errs[0][:300]}"
                     + (" (an ls-sv limit: no proof about such a design can hold)" if "UNSUPPORTED" in errs[0] else ""))
    bad = []
    # (i) ls-sv known and σ_src = σ_rev, every output from the last entry of the first reset; from the same
    # state, the netlist against ls-sv
    for c in range(R - 1, len(stim)):
        src, rev = lrows[c]
        for o, _ in outs:
            if src.get(o) != rev.get(o):
                bad.append((c, f"ls-sv: σ_src and σ_rev disagree on {o}"))
            elif has_xz(src.get(o, "x")):
                bad.append((c, f"ls-sv: {o} is x/z in a claimed snapshot ({o} = {src.get(o)}, MSB first)"))
            elif same and src[o] != net[c][o]:
                bad.append((c, f"{o}: the netlist ({net[c][o]}) is not ls-sv ({src[o]})"))

    def ints(row):
        return {o: int(row[o], 2) for o, _ in outs}
    # (ii) the guarantee, on the netlist's outputs, segment by segment; from different states (i)'s other half,
    # the guarantee on ls-sv's outputs (when (i) found them known)
    runs = [("", net)] + ([] if same or bad else [("ls-sv: ", [lrows[c][0] for c in range(len(stim))])])
    for who, rows_ in runs:
        for k, (sg, (r0, a, b)) in enumerate(zip(segs, spans)):
            for j, why in mod.violations(dict(point), ints(rows_[r0]), sg["entries"],
                                         [ints(rows_[c]) for c in range(a, b)]):
                bad.append((r0 if j < 0 else a + j, f"{who}segment {k} ({sg.get('tag')}), entry {j}: {why}"))
    # (iii) Moore: nothing an output shows moves between two edges
    for c in range(1, len(stim)):
        moved = [o for o, _ in outs if pre[c][o] != net[c - 1][o]]
        if moved:
            bad.append((c, f"{', '.join(moved)} changed before the edge of cycle {c} with the clock low, from the "
                        f"snapshot's {' '.join(net[c - 1][o] for o in moved)} to "
                        f"{' '.join(pre[c][o] for o in moved)} when the inputs changed: a combinational path "
                        "from an input to an output (the task's outputs are Moore, `MooreOut`)"))
    return rec, sorted(bad)


# L5 (TXTASK-V2-REVIEW.md section 12.2; fixed 2026-11-08, the react kind's rule F4 for the transaction kinds): a
# tx/stream statement fixes the payload / the emitted values and bounds WHEN `done` / `out_valid` show them (within the
# latency), but not the cycle itself, so a correct design whose timing within the latency depends on an unreset register
# can show `done` at one cycle from one power-up and at another from another. Check (i) therefore compares the netlist
# with ls-sv bit for bit only where the two start from the SAME state (seed 0, when `zero_starts_agree`); from different
# power-ups it holds ls-sv's own run to what the statement claims of it (`lssv_claims`), while (ii) holds the netlist's
# run to the task's evaluator as before. ls-sv's claims are its guarantee up to its rely horizon: the stimulus is
# realized against the NETLIST's `done` / `out_valid` (the hold and the waits end when the netlist's do), so where
# ls-sv's run is slower the environment stops honouring ls-sv's rely (operands changed before ls-sv's `done` rose, a
# start before ls-sv showed its outputs), and the statement claims nothing from that entry on.


def _lssv_known(lrows, c, o):
    """The failure for ls-sv's output `o` at snapshot `c` (σ_src and σ_rev disagree, or x/z), or None."""
    src, rev = lrows[c]
    if src.get(o) != rev.get(o):
        return f"ls-sv: σ_src and σ_rev disagree on {o}"
    if has_xz(src.get(o, "x")):
        return f"ls-sv: {o} is x/z in a claimed snapshot ({o} = {src.get(o)}, MSB first)"
    return None


def tx_rely_horizon(proto, stim, ltr, R):
    """(h, why): the first entry from the release `R` at which the environment leaves TxTask.Rely for the snapshots
    `ltr` (`TraceBit tr c done true` = `ltr[c][done] == "1"`), or len(stim) and None. Rely at c: a start only when
    Idle (every earlier start was followed, before c, by a snapshot showing done = 1), and the operands of a start held
    at every entry until the first snapshot (from the start's own on) that shows done = 1."""
    st, done, ops = proto["start"], proto["done"], list(proto["operands"])
    open_s = None          # the start whose done has not been shown at a snapshot in [s, c)
    for c in range(R, len(stim)):
        if open_s is not None:
            if stim[c][st] == 1:
                return c, f"the start at entry {c} comes before ls-sv's done rose for the start at entry {open_s}"
            if any(stim[c][o] != stim[open_s][o] for o in ops):
                return c, f"the operands change at entry {c} before ls-sv's done rose for the start at entry {open_s}"
        if stim[c][st] == 1:
            open_s = c
        if open_s is not None and ltr[c].get(done) == "1":
            open_s = None
    return len(stim), None


def stream_rely_horizon(proto, count, stim, ltr, R):
    """(h, why) as `tx_rely_horizon`, for StreamTask.Rely: a start only when Idle (every earlier start has shown its
    `count` outputs at snapshots before c, each with out_valid known and out_data known where valid: `Shows`), and
    in_valid = 1 exactly at the `count` entries after each start."""
    st, iv, ov, od = proto["start"], proto["in_valid"], proto["out_valid"], proto["out_data"]
    open_s, shown, broken = None, 0, False
    for c in range(R, len(stim)):
        if stim[c][st] == 1 and open_s is not None:
            return c, (f"the start at entry {c} comes before ls-sv showed the {count} outputs of the start at entry "
                       f"{open_s} ({shown} shown" + (", then an unknown observation" if broken else "") + ")")
        want = any(stim[s][st] == 1 for s in range(max(R, c - count), c))
        if stim[c][iv] != int(want):
            return c, f"in_valid is {stim[c][iv]} at entry {c}, not {int(want)}"
        if stim[c][st] == 1:
            open_s, shown, broken = c, 0, False
        if open_s is not None and not broken and shown < count:
            v = ltr[c].get(ov)
            if v not in ("0", "1") or (v == "1" and has_xz(ltr[c].get(od, "x"))):
                broken = True
            else:
                shown += v == "1"
        if open_s is not None and not broken and shown >= count:
            open_s = None
    return len(stim), None


def lssv_claims(task, mod, point, stim, lrows, items, R, latency):
    """ls-sv's run (`lrows`, from a power-up other than the netlist's) against what the task's statement claims of
    it (L5, above): (h, why the rely ends or None, the failures [(cycle, why)]). Up to its rely horizon h: `done` /
    `out_valid` known at every snapshot from the release; tx-family: done = 0 before the first start, every start s
    with s + lat < h shows done = 1 at a snapshot in [s, s + lat], and from the first snapshot (from s on) showing
    done = 1 to the next start (or h) done stays 1 with the payload oracle.py's `good` result (TxTask.Guar);
    stream-family: out_valid = 0 before the first start, and every start s with s + lat < h emits, from s to the
    next start (or h), exactly oracle.py's values, none after s + lat, out_data known where valid
    (StreamTask.Guar). The claimed bits also need σ_src = σ_rev."""
    proto, kind = task["protocol"], task["kind"]
    ltr = [src for src, _ in lrows]
    starts = [c for c in range(R, len(stim)) if stim[c][proto["start"]] == 1]
    bad = []
    if kind == "tx-family":
        done, payload = proto["done"], list(proto["payload"])
        h, why = tx_rely_horizon(proto, stim, ltr, R)
        for c in range(R, h):
            w = _lssv_known(lrows, c, done)
            if w:
                bad.append((c, w))
            elif ltr[c][done] == "1" and not (starts and starts[0] <= c):
                bad.append((c, f"ls-sv: done is 1 at cycle {c}, before the first start"))
        for k, s in enumerate(starts):
            if s >= h:
                break
            end = min(starts[k + 1] if k + 1 < len(starts) else len(stim), h)
            fd = next((c for c in range(s, end) if ltr[c].get(done) == "1"), None)
            if s + latency < h and (fd is None or fd > s + latency):
                bad.append((s, f"ls-sv: transaction {k} ({items[k].get('tag')}): done did not rise within the "
                            f"declared latency {latency} of its start entry (cycle {s})"))
                continue
            for c in range(fd if fd is not None else end, end):
                if _lssv_known(lrows, c, done):
                    continue                    # reported above
                ws = [w for w in (_lssv_known(lrows, c, p) for p in payload) if w]
                if ws:
                    bad.append((c, ws[0]))
                elif ltr[c][done] != "1":
                    bad.append((c, f"ls-sv: transaction {k}: done fell at cycle {c}, before the next start"))
                else:
                    res = {p: int(ltr[c][p], 2) for p in payload}
                    if not mod.good(dict(point), items[k], res):
                        why_ = getattr(mod, "mismatch", lambda *a: None)(dict(point), items[k], res)
                        bad.append((c, f"ls-sv: transaction {k}: the payload is not the task's result: {why_ or res}"))
        return h, why, bad
    ov, od, count = proto["out_valid"], proto["out_data"], int(point[proto["count"]])
    h, why = stream_rely_horizon(proto, count, stim, ltr, R)
    for c in range(R, h):
        w = _lssv_known(lrows, c, ov)
        if w:
            bad.append((c, w))
        elif ltr[c][ov] == "1" and not (starts and starts[0] <= c):
            bad.append((c, f"ls-sv: out_valid is 1 at cycle {c}, before the first start"))
    for k, s in enumerate(starts):
        if s + latency >= h:
            break
        if s + count >= len(stim):        # the values are not all in the stimulus: nothing is claimed
            continue
        end = min(starts[k + 1] if k + 1 < len(starts) else len(stim), h)
        tag, vals, ok = items[k].get("tag"), [], True
        for c in range(s, end):
            w = _lssv_known(lrows, c, ov) or (_lssv_known(lrows, c, od) if ltr[c][ov] == "1" else None)
            if w:
                bad.append((c, w))
                ok = False
                break
            if ltr[c][ov] == "1":
                if c - s > latency:
                    bad.append((c, f"ls-sv: transaction {k} ({tag}): out_valid is 1 at cycle {c}, {c - s} cycles "
                                f"after its start entry (cycle {s}): beyond the declared latency {latency}"))
                    ok = False
                    break
                vals.append(int(ltr[c][od], 2))
        if ok and not mod.good(dict(point), items[k], {"out": vals}):
            why_ = getattr(mod, "mismatch", lambda *a: None)(dict(point), items[k], {"out": vals})
            bad.append((s, f"ls-sv: transaction {k} ({tag}): the emitted values are not the task's: {why_ or vals}"))
    return h, why, bad


def clocked_seed(task, mod, point, point_s, seed, cfg, latency, envl, exe, nports, work, deadline, zeros_agree=True):
    """One seed: (the record, the failures [(cycle, why)]). `zeros_agree`: `zero_starts_agree` of the scored record
    (seed 0 then starts the netlist and ls-sv from the same state)."""
    clk, kind, R = task["clock"], task["kind"], cfg["reset_cycles"]
    ins = sorted((n, w) for d, n, w in nports if d == "input")
    outs = sorted((n, w) for d, n, w in nports if d == "output")
    dins = [(n, w) for n, w in ins if n != clk]
    draw = seed_draw(task, point_s, seed)
    lines, items = clocked_plan(task, mod, point, seed, cfg, dins, draw["rng"])
    rows, late, el, err = vl_run_clocked(exe, dins, outs, lines, seed, draw, latency or 0, work,
                                         max(60.0, deadline - time.time()))
    if rows is None:
        raise Reject(f"the scored netlist does not simulate: {err}")
    stim = [lines[li][1] for li, _ in rows]
    net = [r for _, r in rows]
    start = start_of(seed, draw)
    rec = {"seed": seed, "seed_sha256": draw["seed_sha256"], "salted": draw["salted"], "reset_cycles": R,
           "cycles": len(stim), "late": late, "t_netlist_run_s": round(el, 3),
           "netlist_randreset": start[0], "netlist_randseed": draw["vl_seed"], "lssv_start": start[1]}
    # L5 (above): bit for bit only from the same state; seq-family's claim fixes every output, so it compares always
    same = kind not in LATENCY_KINDS or (seed == 0 and zeros_agree)
    if kind in LATENCY_KINDS:
        rec["compared"] = ("the netlist with ls-sv, bit for bit on the cared outputs (the same all-zeros start)" if same
                           else "each run with the guarantee (the netlist and ls-sv start from different power-ups)")
    lports, lrows, _, _, el = lssv_eval(envl, point_s, ins, [{clk: 0, **e} for e in stim], cfg["fuel"],
                                        work, deadline, trace=True, start=start[1])
    rec["t_lssv_s"] = round(el, 2)
    if lports != nports:
        raise Reject(f"the ports differ: ls-sv has {sorted(lports)}, the netlist {sorted(nports)}")
    errs = [r[1] for r in lrows if r[0] == "ERROR"]
    if errs:
        raise Reject(f"ls-sv does not complete the run (seed {seed}): {errs[0][:300]}"
                     + (" (an ls-sv limit: no proof about such a design can hold)" if "UNSUPPORTED" in errs[0] else ""))
    cares, bad, payload = [set() for _ in stim], [], [n for n, _ in outs]
    if kind == "tx-family":
        proto, done = task["protocol"], task["protocol"]["done"]
        payload = list(proto["payload"])
        starts = [c for c in range(R, len(stim)) if stim[c][proto["start"]] == 1]
        for c in range(R, len(stim)):
            cares[c].add(done)
            if net[c][done] == "1" and not (starts and starts[0] <= c):
                bad.append((c, f"done is 1 at cycle {c}, before the first start"))
        rec["transactions"] = log = []
        for k, s in enumerate(starts):
            nxt = starts[k + 1] if k + 1 < len(starts) else len(stim)
            fd = next((c for c in range(s, nxt) if net[c][done] == "1"), None)
            log.append({"tag": items[k].get("tag"), "start": s, "first_done": fd,
                        "latency": None if fd is None else fd - s, "hold": None if fd is None else [fd, nxt - 1],
                        "samples": 0 if fd is None else nxt - fd})
            if fd is None or fd - s > latency:
                bad.append((s, f"transaction {k} ({items[k].get('tag')}): done did not rise within the "
                            f"declared latency {latency} of its start entry (cycle {s})"))
                continue
            for c in range(fd, nxt):
                cares[c].update(payload)
                res = {p: int(net[c][p], 2) for p in payload}
                if net[c][done] != "1":
                    bad.append((c, f"transaction {k}: done fell at cycle {c}, before the next start"))
                elif not mod.good(dict(point), items[k], res):
                    why = getattr(mod, "mismatch", lambda *a: None)(dict(point), items[k], res)
                    bad.append((c, f"transaction {k}: the payload is not the task's result: {why or res}"))
    elif kind == "stream-family":
        proto = task["protocol"]
        ov, od = proto["out_valid"], proto["out_data"]
        starts = [c for c in range(R, len(stim)) if stim[c][proto["start"]] == 1]
        for c in range(R, len(stim)):
            cares[c].update([ov, od] if net[c][ov] == "1" else [ov])
            if net[c][ov] == "1" and not (starts and starts[0] <= c):
                bad.append((c, f"out_valid is 1 at cycle {c}, before the first start"))
        rec["transactions"] = log = []
        for k, s in enumerate(starts):
            nxt, tag = starts[k + 1] if k + 1 < len(starts) else len(stim), items[k].get("tag")
            got = [c for c in range(s, nxt) if net[c][ov] == "1"]
            vals = [int(net[c][od], 2) for c in got]
            log.append({"tag": tag, "start": s, "outputs": len(got), "first_output": got[0] if got else None,
                        "last_output": got[-1] if got else None, "latency": got[-1] - s if got else None})
            over = [c for c in got if c - s > latency]
            if over:
                bad.append((over[0], f"transaction {k} ({tag}): out_valid is 1 at cycle {over[0]}, {over[0] - s} "
                            f"cycles after its start entry (cycle {s}): beyond the declared latency {latency}"))
            elif not mod.good(dict(point), items[k], {"out": vals}):
                why = getattr(mod, "mismatch", lambda *a: None)(dict(point), items[k], {"out": vals})
                bad.append((s, f"transaction {k} ({tag}): the emitted values are not the task's: {why or vals}"
                            + (f"; the run stops: no more outputs within the declared latency {latency}"
                               if late and k == len(starts) - 1 else "")))
    else:
        exp = mod.expect(dict(point), stim)
        for c in range(len(stim)):
            if exp[c] is None:
                continue
            cares[c].update(payload)
            got = {o: int(net[c][o], 2) for o in exp[c]}
            if got != exp[c]:
                bad.append((c, f"the outputs {got} are not the task's {exp[c]}"))
    if not same:
        # (i) from different power-ups: ls-sv's run against what the statement claims of it (L5, `lssv_claims`)
        h, why, lbad = lssv_claims(task, mod, point, stim, lrows, items, R, latency)
        rec["lssv_claimed_to"] = h
        rec["lssv_rely_ends"] = why
        return rec, sorted(bad + lbad)
    for c, (src, rev) in enumerate(lrows):
        for o in sorted(cares[c]):
            if src.get(o) != rev.get(o):
                bad.append((c, f"ls-sv: σ_src and σ_rev disagree on {o}"))
            elif has_xz(src.get(o, "x")):
                bad.append((c, f"ls-sv: {o} is x/z in a cared position ({src.get(o)})"))
            elif src[o] != net[c][o]:
                bad.append((c, f"{o}: the netlist ({net[c][o]}) is not ls-sv ({src[o]})"))
    return rec, sorted(bad)


def run_clocked(task, envl, netlist, sres, work, mod, point, latency=None, mode=None):
    """The clocked check (above) of the scored `netlist` at `point` (a dict), `mod` the task's oracle
    module (`clocked_oracle`), `latency` the declared n (tx-family). Returns the record; raises Reject
    (the record in `.info["record"]`) or InfraError."""
    t_start, cfg, top = time.time(), config(task), task["top"]
    if task["kind"] not in CLOCKED_KINDS or "reset" not in task:
        raise InfraError(f"the clocked post-synthesis check covers the kinds {CLOCKED_KINDS} with "
                         f"a task.json `reset` (this is {task['kind']})")
    if task["kind"] in LATENCY_KINDS and not latency:
        raise InfraError(f"the clocked post-synthesis check of a {task['kind']} task needs the declared latency")
    point_s = envelope.point_str(point)
    rec = {"kind": task["kind"], "point": point_s or "default", "mode": resolve_mode(mode),
           "netlist_sha256": sha256_file(netlist), "envelope_sha256": sha256_file(envl),
           "sveval_sha256": sha256_file(SVEVAL) if os.path.isfile(SVEVAL) else None,
           "fuel": cfg["fuel"], "latency": latency, "oracle_sha256": sha256_file(mod.__file__), "seeds": []}
    deadline = t_start + float(cfg["time_limit_s"])
    try:
        _, rec["verilator"], _ = verilator_info()
        design, drivers = reread_check(netlist, top, sres, work)
        unread, readers = unknown_bits(design, top)
        xlit = unknown_message(unread, readers, unknown_names(sres) if readers else None,
                               read_unknown(drivers, top) if readers else None)
        if xlit:
            raise Reject(xlit)
        if unread:
            rec["netlist_unread_unknown"] = unread
            print(unread_note(unread), file=sys.stderr, flush=True)
        nports = netlist_ports(design, top)
        ins = sorted((n, w) for d, n, w in nports if d == "input")
        outs = sorted((n, w) for d, n, w in nports if d == "output")
        if task["clock"] not in dict(ins):
            raise Reject(f"the netlist has no clock input `{task['clock']}`")
        proto, done = task.get("protocol") or {}, "false"
        if task["kind"] == "tx-family":
            done = f"top->{ccode_ident(proto['done'])} != 0"
        elif task["kind"] == "stream-family":      # the count-th out_valid = 1 since the start row
            done = (f"[&]{{ static long n = 0; n = (kind[0] == 'S' ? 0 : n) + (top->{ccode_ident(proto['out_valid'])}"
                    f" != 0); return n >= {int(point[proto['count']])}; }}()")
        harness = (harness_cpp([p for p in ins if p[0] != task["clock"]], outs, REACT_HARNESS,
                               clk=ccode_ident(task["clock"])) if task["kind"] == "react-family" else
                   harness_cpp([p for p in ins if p[0] != task["clock"]], outs, CLOCKED_HARNESS,
                               clk=ccode_ident(task["clock"]), done=done))
        exe, el, err = vl_build([netlist, simcells()], top, {}, ins, outs, work, "clocked",
                                max(120.0, deadline - time.time()), harness=harness, xflags=VL_X_CLOCKED)
        rec["t_netlist_build_s"] = round(el, 2)
        if exe is None:
            raise Reject(f"the scored netlist does not compile: {err}")
        bad = []
        for seed in range(cfg["seeds"]):
            if task["kind"] == "react-family":
                srec, sbad = react_seed(task, mod, point, point_s, seed, cfg, envl, exe, nports, work, deadline,
                                        zeros_agree=zero_starts_agree(sres))
            else:
                srec, sbad = clocked_seed(task, mod, point, point_s, seed, cfg, latency, envl, exe, nports,
                                          work, deadline, zeros_agree=zero_starts_agree(sres))
            rec["seeds"].append(srec)
            bad += [(seed, c, why) for c, why in sbad]
        rec["mismatches"] = len(bad)
        if bad:
            rec["report"] = [{"seed": s, "cycle": c, "why": w} for s, c, w in bad[:REPORT_MAX]]
            raise Reject(f"{len(bad)} failures at {point_s or 'default'} (reset for {cfg['reset_cycles']} "
                         "cycles from a power-up state: seed 0 all zeros, the others random; cycle = stimulus entry"
                         + (f"; segments of oracle.py `segments`, the last {cfg['long']} entries long"
                            if task["kind"] == "react-family" else "") + "):\n"
                         + "\n".join(f"  seed {s}, cycle {c}: {w}" for s, c, w in bad[:8]))
    except Reject as r:
        rec["seconds"] = round(time.time() - t_start, 2)
        r.info["record"] = rec
        raise
    rec["seconds"] = round(time.time() - t_start, 2)
    return rec


def bug_report(rec, task, point_s):
    """The rejection, written as the bug report it is."""
    outs = rec.get("outputs", [])

    def show(d):
        return " ".join(f"{k}={d[k]}" for k in outs if k in d)

    lines = [f"BUG REPORT (task {task['name']}, point {point_s or 'default'}; envelope sha256 "
             f"{rec['envelope_sha256'][:16]}, netlist sha256 {rec['netlist_sha256'][:16]}; "
             f"seed {rec.get('seed', '?')[:16]}). The proof is about ls-sv's reading of the "
             "design and the score about Yosys's; on these vectors they differ:"]
    for e in rec.get("report", [])[:5]:
        lines.append(f"  vector {e['vector']}: " + " ".join(f"{k}={v}" for k, v in
                                                          e["inputs"].items()))
        if e["lssv_src"] is not None:
            lines.append("    ls-sv (σ_src)  " + show(e["lssv_src"]))
            if e["lssv_rev"] != e["lssv_src"]:
                lines.append("    ls-sv (σ_rev)  " + show(e["lssv_rev"]))
        else:
            lines.append(f"    ls-sv          {e['lssv_error']}")
        lines.append("    netlist        " + show(e["netlist"]))
        if e["verilator_rtl"] is not None:
            lines.append("    Verilator RTL  " + show(e["verilator_rtl"]))
        lines.append(f"    {'; '.join(e['why'][:4])}. Verdict: {e['verdict']}")
    more = rec["mismatches"] - min(5, len(rec.get("report", [])))
    if more > 0:
        lines.append(f"  ... and {more} more failing vectors (the result's `report` lists "
                     f"{len(rec.get('report', []))})")
    lines.append(f"Reproduce: python3.12 check/postsynth.py --task tasks/{task['name']} DESIGN.sv"
                 + (f" --point {point_s}" if point_s else "")
                 + (f" --mode {rec['mode']}" if rec.get("mode") else "")
                 + " --keep DIR (with the same $SVGOLF_POSTSYNTH_SALT); DIR holds the netlist, "
                 "the vectors and every "
                 "simulator's output. Is it ls-sv or Yosys that is wrong? File it either way: "
                 "README.md, \"Rules\".")
    return "\n".join(lines)


# ---------------------------------------------------------------- standalone

def check_design(task_dir, sv, work, point=None, third_all=False, random_count=None, gate=True,
                 mode=None):
    """Gate, extract, score (keeping the netlist) and check `sv` for the task
    at `point` (default: the scoring point). Returns the record; raises
    Reject / InfraError / envelope.Refused / score.ScoreError.

    `gate=False` is RESEARCH ONLY: the file's text with its comments
    stripped, but none of the gate's refusals applied, stands in for the
    canonical text, so a construct the gate refuses (`unique case`) reaches
    this check, to measure what the check alone would say about it."""
    mode = resolve_mode(mode)     # a bad $SVGOLF_POSTSYNTH fails before any work
    task = envelope.load_task(task_dir)
    params = ({k: int(v) for k, v in task["scoring"]["params"].items()} if point is None
              else dict(point))
    # The point itself is the only probe point: the envelope's design does not
    # depend on the probe points (they only add the sidecar that the checker's
    # `design` stage cross-checks), and every extra point costs an extraction.
    pts = [params] if params else []
    if gate:
        ex = envelope.extract(sv, task["top"], pts, os.path.join(work, "extract"))
    else:
        ex = extract_ungated(sv, task["top"], pts, os.path.join(work, "extract"))
    netlist = os.path.join(work, "netlist.v")
    sres = score.score([ex["canonical"]], task["top"], params, gate=False, netlist_out=netlist)
    rec = run(task, ex["canonical"], ex["envelope"], netlist, sres, work, point=params,
              third_all=third_all, random_count=random_count,
              oracle=load_oracle(task_dir, task), mode=mode)
    rec["score"] = {k: sres[k] for k in ("area_ge", "area_mge", "depth", "gates")}
    return rec


def extract_ungated(sv, top, pts, out_dir):
    """`envelope.extract` without the source gate's REFUSALS (research only):
    the gate's comment stripping (`srcgate.strip_comments`) still makes the
    canonical text, but a construct the gate refuses (`unique case`) passes."""
    import srcgate
    with open(sv) as fh:
        text, _ = srcgate.strip_comments(fh.read())
    os.makedirs(out_dir, exist_ok=True)
    canon = os.path.join(out_dir, os.path.basename(sv))
    with open(canon, "w") as fh:
        fh.write(text)
    env = canon + ".json"
    proc, cmd = envelope.run_extractor(canon, top, pts, env)
    if proc.returncode != 0 or not os.path.exists(env):
        raise envelope.Refused("extract", "the extractor refused the design:\n"
                               + envelope.tail(proc.stderr + proc.stdout))
    return {"canonical": canon, "envelope": env}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("design")
    ap.add_argument("--task", required=True, help="the task directory")
    ap.add_argument("--point", help="a parameter point, e.g. N=32 (default: the scoring point)")
    ap.add_argument("--mode", choices=MODES,
                    help=f"light (a subset of the vectors) or full; default: ${MODE_ENV}, "
                    f"else {DEFAULT_MODE}")
    ap.add_argument("--random", type=int, help="override the task's random vector count")
    ap.add_argument("--third-all", action="store_true",
                    help="audit: Verilator on the RTL for EVERY vector (ls-sv vs Verilator too)")
    ap.add_argument("--keep", help="keep the work directory here")
    ap.add_argument("--no-gate", action="store_true",
                    help="RESEARCH ONLY: skip the source gate's refusals (comments are "
                    "still stripped), to see what this check alone says")
    ap.add_argument("--json", help="also write the record here")
    args = ap.parse_args(argv)
    work = os.path.abspath(args.keep) if args.keep else tempfile.mkdtemp(prefix="svgolf-ps-")
    os.makedirs(work, exist_ok=True)
    point = envelope.parse_point(args.point) if args.point else None
    out, code = {}, 0
    try:
        out = {"ok": True, "record": check_design(args.task, args.design, work, point,
                                                  args.third_all, args.random,
                                                  gate=not args.no_gate, mode=args.mode)}
    except Reject as r:
        out, code = {"ok": False, "stage": "postsynth", "error": r.msg,
                     "record": r.info.get("record")}, 1
    except envelope.Refused as r:
        out, code = {"ok": False, "stage": r.stage, "error": r.msg}, 1
    except score.ScoreError as e:
        out, code = {"ok": False, "stage": "score", "error": str(e)}, 1
    except (InfraError, envelope.InfraError) as e:
        out, code = {"ok": False, "stage": "infrastructure", "error": str(e)}, 2
    finally:
        if not args.keep:
            shutil.rmtree(work, ignore_errors=True)
    w = functional_warning(((out.get("record") or {}).get("functional")))
    if w:
        print(w, file=sys.stderr)
    text = json.dumps(out, indent=2, sort_keys=True)
    print(text)
    if args.json:
        with open(args.json, "w") as fh:
            fh.write(text + "\n")
    return code


if __name__ == "__main__":
    sys.exit(main())
