#!/usr/bin/env python3.12
"""svGolf checker v0: check one submission against one task, then score it.

    python3.12 check.py TASK_DIR solution.sv Solution.lean [--json OUT]
    python3.12 check.py TASK_DIR solution.sv --unproved      # every check but the proof
    python3.12 check.py TASK_DIR solution.sv --unproved --tactics   # ... and can the tactics read it?

(The file names and paths are free; what is fixed is the Lean file's content: the checker stages it as the
module `Submission.Solution`, which must `import Submission.Design` and prove the theorem below.)

A submission is a SystemVerilog file and a Lean file. The Lean file proves

    theorem Submission.solution : Submission.Goal

where `Submission.Goal` is the task's statement about the design that the
checker extracts from solution.sv (README.md, "Submitting"). Stages, in
order; the first failing stage rejects:

  task          read TASK_DIR/task.json; its `kind` (`KINDS`): combinational, or CLOCKED
                (`seq-family`, `tx-family`, PLAN4 Gate 2; `stream-family`, C8;
                `react-family`, the reactive kind `ReactTask` of SvGolf/TaskReact.lean:
                the task names its `clock`; its score, postsynth and ppa stages are the
                clocked ones, `score_clocked`)
  latency       (tx-family, stream-family: `LATENCY_KINDS`) the solution's one header
                line `-- svgolf-latency: n`
                (n ≥ 1); the goal is then `Goal lat := Statement design.sem lat ∧
                lat p₀ = n` for the solution's definition `Submission.lat`, and the
                result records `latency: n`. Any other kind refuses the line. After the
                comparator, the kernel's value of `Submission.lat p` at every point p of
                the clocked post-synthesis check (F8, decided 2026-11-08; `latency_at`):
                each point is checked against its own latency (`--unproved`:
                `--latency-at POINT:n`, else n)
  imports       the Lean file's imports are on the allowlist (Mathlib and the packages
                it imports are: PACKAGE_ROOTS; for such a solution the `trusted` stage
                ends with a probe that compiles the package imports ALONE: a module the
                player named that no package has a source for is a rejection here, a
                package or module missing from the machine an infrastructure error, see
                `classify_import_probe`). Checked AGAIN after the comparator against the
                imports Lean recorded in the compiled solution (`import_mismatch`): a
                header the checker read differently from Lean is rejected
  source        score/srcgate.py: no preprocessor directives, attributes,
                synthesis-pragma comments or unique/priority qualifiers, no
                x/z literal digit outside a casez/casex item wildcard, no
                host access ($readmemh, $fopen, $system, $value$plusargs,
                $dumpfile, DPI, ...: the checker runs untrusted text on the
                organizer's machine);
                every later stage (extractor, banlist, Yosys) reads the
                gate's CANONICAL text (comments stripped), so the program
                that is proved and the program that is scored are one text.
                A clocked kind adds the clocked rules (srcgate.py item 6: one
                clock, `always_ff @(posedge clk)` only, synchronous reset, no
                initial/initializer/latch/delay/wait/fork/extra event, no
                blocking assignment in always_ff)
  extract       the PINNED lean-surfaces extractor writes the envelope and the
                multi-point probe sidecar (`--probe-points`: the task's probe
                points plus the scoring and backstop points, always) from the
                canonical text; a player's .json is never read. The source
                gate and the extractor run through `check/envelope.py`, svGolf's
                ONE extraction path (`load_sv` uses it too). The top
                module's parameters (ParameterDecl, not localparam) must be
                exactly the task's, by name and order.
  banlist       score/banlist.py: pyslang front check + Yosys backstop (the task's operators and
                the run-time / % ** every task bans)
  fourstate     score/fourstate.py at EVERY point the checker probes (`fourstate_points`:
                the scoring point first, then the task's probe and backstop points;
                since 2026-11-06, before at the scoring point only): no x or z value
                can arise there (no parameter or constant expression with unknown
                bits, no constant or run-time select that can leave its range, no
                undriven or conflicting net, no logic loop: Yosys `check`; the x/z
                LITERALS are the source gate's, run-time `/ % **` the banlist's).
                ls-sv computes with x as IEEE 1800 simulation does, Yosys resolves
                it as a don't-care, so these sources are refused at those points.
                SCOPE: the statement covers every parameter value in range, and a
                point nobody probes is not checked; this narrows the gap until
                ls-sv's every-resolution semantics lands, it does not close it
  clocked_rules (a clocked kind) check/clocked_rules.py: Python twins of txtask-v2's
                rules on the envelope at every probe point, early refusals with a
                message per construct (the statement and the pinned flow stay the
                authority): rule 3's twin (`XSafe`, decided 2026-11-06) refuses a
                run-time `/` or `%` by a divisor that reads a signal, `**` with a
                signed exponent over a base that reads one, a run-time index that
                mentions a signal declared signed, a run-time bit select whose
                index can leave the vector, a run-time indexed part-select read,
                and an x/z literal outside a casez/casex item at the case's width;
                ADVISORY (one line in `warnings`, never a refusal): a
                register every write of which is its own value (the `score` stage
                refuses it where the flow removes its flip-flop while it is read)
  trusted       `lake build` of the trusted svGolf modules and of the ls-sv
                evaluator `svgolf-eval` (not timed)
  design        compile the GENERATED module `Submission.Design`:
                `load_design_sv2 design from <envelope>` and
                `abbrev Goal : Prop := <task statement> design.sem`. Loader
                refusals (cross-checks, one-driver rule) reject here, and so
                does a design that loads but carries an `Unsupported` node (a
                user function call, a latch: ls-sv cannot run it, so no proof
                can hold): the module ends with an `#eval` testing
                `Design2.hasUnsupported` at the scoring point and the smaller
                probe points, naming the first loud node (WP-C3)
  solution      compile Solution.lean as `Submission.Solution`, under the
                task's time limit, which counts the CPU seconds of the Lean
                process tree (user + system, every thread; decided
                2026-11-05), never the wait for a Lean wrapper, with a
                wall-clock BACKSTOP of SOLUTION_WALL_FACTOR times the limit
                for a proof that sleeps or blocks (`stages.solution`:
                `cpu_seconds`, `seconds` of wall clock, `stopped_by`); with
                `trace.Kernel` on and a pseudo-terminal as Lean's stdout: a
                compile stopped at a limit still says which declaration the
                kernel finished last, and when (`stages.solution.progress`;
                `PROGRESS_OPTION`)
  integrity     the staging tree, the trusted files (the svgolf-eval binary
                and simcells.v included), the svGolf and LeanModels.Sv
                builds, the Lean SEARCH PATH (`lake env printenv LEAN_PATH`): the
                `.olean*` files of the package builds on it (Mathlib and friends), its
                entries' top-level names and its absent entries, for every solution,
                the Lean toolchain, Yosys, and Verilator (its
                binaries and its whole VERILATOR_ROOT, the runtime every model
                is compiled against) with the C++ compiler and make are
                unchanged by the solution's build (checked again after
                postsynth; a tripwire, not a sandbox)
  comparator    check/Comparator.lean: the kernel accepts
                `theorem _ : Submission.Goal := Submission.solution`; axioms
                within the task's allowed set; no extern/implemented_by; the
                toolchain's modules come from the toolchain; the dependency
                closure of the solution and the goal (packages included) is
                replayed through the kernel (under the task's
                `verify_time_limit_s`, CPU seconds as for `solution`, with
                its wall-clock backstop of VERIFY_WALL_FACTOR times it)
  leanchecker   kernel replay of the submission's modules (environment
                hacking; under the same limit and backstop)
  score         score/score.py at the task's scoring point (the two-stage
                canonical flow), keeping the scored gate netlist. A clocked
                kind refuses a NEVER-LOADED REGISTER here (`never_loaded`, txtask-v2,
                decided 2026-11-06) exactly where the flow's own log shows it
                removing a flop whose readers stay (D = Q, a never-active
                enable, a constant clock, or an x constant), or connecting the
                reads of an array lane no write loads to an undefined value
                (opt_mem), at the scoring point and at every postsynth point it
                synthesizes
                (a backstop refuses a state register re-implemented as an FSM:
                the clocked flow runs `synth -nofsm`, so this never fires)
  postsynth     check/postsynth.py: ls-sv (`svgolf-eval`: `design.sem` at the
                scoring point, `run2`) and the SCORED netlist (Verilator: a
                2-state C++ model of the netlist, built once per run) agree on
                every vector of the run's set (fixed corners, task corners,
                harvested comparison constants, seeded random vectors); fail
                closed (x/z in ls-sv's outputs, an unknown constant in the
                netlist, a netlist Verilator will not lint/compile/run
                cleanly, a run that does not complete, σ_src ≠ σ_rev, a port
                difference all reject); a rejection is a bug report. TWO
                MODES: `light` (the default, for local feedback: a
                deterministic SUBSET of the full vectors, seconds instead of
                minutes on the big multipliers) and `full` (the task's whole
                budget: what competitions, `leaderboard.py add`/`verify` and
                `tests/run.py` run). `--postsynth {light,full}` or
                $SVGOLF_POSTSYNTH selects it; the result says which ran
                (`stages.postsynth.mode`). A CLOCKED kind runs the clocked check
                instead (`run_clocked`: power-up states (seed 0 all zeros on both
                sides, the others random), reset, the task's
                oracle.py transactions, ls-sv `--trace` vs the netlist cycle by
                cycle, the oracle's result binding; for `react-family` the
                oracle's segments with a long reset-free run, its guarantee on
                the netlist's outputs and a Moore sample before every edge) at
                each `postsynth.points`
  ppa           score/ppa.py (WP-X3): the sky130 columns of the very netlist the
                score stage kept and postsynth verified (area in um^2, delay in ps,
                unit depth, cell histogram, with the inputs' hashes), as the result
                key `ppa`. Flow A0' is the RANKED score (decided 11/03): its area x
                delay is the one number Par, Record and Under par use (leaderboard/
                combined.py); the GE and depth of `score` and flow A1' (`mapped`,
                below) are extra columns. Every other field is untouched. `--ppa {auto,off,
                require}`: `auto` (the default) weighs the netlist when the
                pinned liberty is present and otherwise records
                `ppa: {"available": false, "reason": ...}` with one line on
                stderr; `require` makes an absent, unreadable or wrong liberty
                an infrastructure error (competitions, `leaderboard.py add`/
                `verify --full` and `tests/run.py` with the liberty use it);
                `off` has no `ppa` key and no stage. sky130_a0_v3 (11/04): the
                weighed netlist is the A0' one REPAIRED by buffering only
                (buffer trees on every net over its driver's limits, inputs,
                flop Q nets and output bits included, the tie cell replicated;
                inputs driven by the task's `input_drive`, default
                sky130_fd_sc_hd__buf_8), and a netlist the repair cannot make
                ELECTRICALLY LEGAL (a load over max_capacitance, a transition
                over max_transition, a timing-table read outside its range)
                is REJECTED at this stage, the net named in the error and in
                `ppa.reason` (`ppa.illegal: true`): nothing is extrapolated.
                Any other design the pinned flow cannot weigh
                carries its reason in `ppa` and never fails the
                check; infrastructure errors (exit status 2) are only a
                liberty that `require` cannot open, in `require` a defect of
                ppa.py or a depth/gate-count disagreement with the score
                stage or a repaired netlist that is not the scored circuit,
                and in every mode a netlist file that is not the one
                postsynth verified (sha256), and a task whose `input_drive` is
                not one of the pins' allowed cells (reported before any stage,
                by every run that weighs). The liberty (12.8 MB) is fetched,
                not vendored: `python3.12 score/ppa.py --fetch-liberty`;
                score/PPA.md. WP-X4: `ppa` also carries `mapped`, flow A1' (a
                real `abc -liberty` mapping of the canonical RTLIL of the same
                score run, one more Yosys process of about 0.5 to 3 s, checked
                against the scored netlist on a sample of input vectors, then
                weighed by the same STA): `area_um2_sky130_mapped_v1`,
                `mapped_delay_sky130_v1`, cells, histogram, levels, with its own
                version and hashes; `{"available": false, "reason": ...}` for a
                design it cannot map (never a failure of the check); A1' is an
                extra column, never ranked. `--ppa` semantics are unchanged

Prints the result JSON (`accepted`, `stage`, `errors`, per-stage details,
`score`, and `ppa` unless `--ppa off`). An accepted result also says whether the check was COMPLETE
(`complete`; `incomplete`, the reasons, when it was not: `incomplete_reasons`): a run with `--no-score`,
a LIGHT post-synthesis check, `--no-trusted-build` or a `--time-limit` other than the task's left part
of the check out, so it establishes nothing a board may rank (README.md, "Rules": a failed, timed-out or
incomplete check establishes nothing); `leaderboard.py add` refuses it (a light one only as a marked
light record, which never ranks). Exit status: 0 accepted (or a clean
`--unproved` run, below), 1 rejected (a stage failed), 2 usage or
infrastructure error.

On stderr, one line when each long stage starts (`check: <stage> ...`), the
result lines of the tactics, solution, postsynth and ppa stages, and, as the
LAST line of every run that reached the `ppa` stage, the ranked headline:

    ranked (sky130 A0'): <area> um^2 x <delay> ps = <area x time> um2*ns; par <par> (<par reference>)

(`par` is the best proved reference's area x time on the task's board, the reference player's records in
leaderboard/data, leaderboard.py `par_of`; `par: none recorded` without one), or `ranked: liberty missing, run
python3.12 score/ppa.py --fetch-liberty` when the pinned liberty cannot be opened, or `ranked: not computed: <why>`
when the pinned flow cannot weigh the netlist. On a clocked task <delay> is the ranked time, cycles x the period.

`--unproved` (no Lean file) runs every stage that does not need a proof
(source, extract, banlist, fourstate, trusted, design, score, postsynth, ppa) and NEVER
accepts: a design that passes them all stops at the pseudo-stage `unproved`,
with `accepted: false`, no `errors`, the sentence that says so in `notes`,
`unproved_ok: true` and exit status 0 (a failed stage: exit 1, as for a full run).
It answers "is this design admissible, and what does it score?" before a
proof exists; `tests/run.py` uses it for the postsynth attacks, which have no
proof. With `--keep` or `--stage-dir`, its `dev_hint` is the command that
compiles ANY probe file (`<YourFile>.lean`, which starts with `import
Submission.Design`) against the staged design.

ADVISORY output, which never changes `accepted`, `stage` or another field:
  * `stages.postsynth.functional` and one line of the top-level `warnings`
    (also on stderr for `--unproved`): the design disagrees with the task's
    Python oracle (`oracle.py`, task.json `oracle`) on some of the postsynth
    vectors (check/postsynth.py, "FUNCTIONAL SMOKE CHECK");
  * `--unproved --tactics`: `tactics` = {"in_fragment": true|false|null,
    "message": "ok" or the first line of the tactic's refusal}, from one extra
    Lean job (`sv_structure?` on the staged design; `stages.tactics.seconds`).

SANDBOX (WP-S): `--sandbox {off,auto,require}` (default `auto`, $SVGOLF_SANDBOX). Every process that
runs submitted text -- the Lean compiles (the generated design module, the import probe, the solution),
the comparator and `leanchecker`, the extractor, Yosys, Verilator and its C++ build, the compiled model,
`svgolf-eval` -- runs under the operating system's sandbox (macOS Seatbelt, Linux bubblewrap;
check/sandbox/): no network, no reads outside its inputs, no writes outside one fresh output directory
(the checker adopts the `.olean`), no other program, a scrubbed environment (the competition salt is
invisible), and the supervisor's wall-clock, memory, output and file-size limits. `auto` uses it when
the mechanism exists and passes its self-test and says on stderr when it does not; `require` makes that
an infrastructure error (official runs; `leaderboard.py add`/`verify` use it); `off` runs without it. The
result gets `sandbox` (mode, mechanism, active) and `stages.sandbox` (what ran inside it, the profiles'
digests, the self-test); `--sandbox off` adds neither key. `lake env` runs ONCE, outside, and the
toolchain's `lean` then runs directly (lake runs git in every package checkout). Slot wrappers
(`--lean-wrap`) stay outermost: slot, supervisor, sandbox, program.

Environment:
  SVGOLF_LEAN_WRAP  command prefix for every lake/lean invocation (e.g. a
                    slot-limiting wrapper); --lean-wrap overrides. Each Lean
                    stage's record then has `waited`: the seconds its calls spent
                    before the command started (the wrapper's queue), which its
                    `seconds` never include
  SVGOLF_LEAN_WRAP_ONCE  `1` (with a wrapper set): take the wrapper ONCE, around
                    the whole run (check.py re-runs itself behind it, and the run
                    inside calls lake and lean directly), instead of once per
                    lake/lean call; the result then has `lean_wrap: {"once": true,
                    "waited": s}`. The per-call wrapping stays the default
  SVGOLF_SANDBOX    `off`, `auto` (default) or `require`; --sandbox overrides
  SVGOLF_SANDBOX_RSS_MB, _OUT_MB, _FSIZE_MB   the supervisor's limits per sandboxed process (defaults:
                    60% of the RAM up to 12 GB; 16 MB of Lean output, 64 MB of a tool's; 2 GB and 4 GB
                    files)
  SVGOLF_LS_ROOT    the lean-surfaces checkout (default: the parent directory when svGolf
                    sits inside lean-surfaces, else .lake/packages/lean-models: check/layout.py)
  SVGOLF_PACKAGES   the Lake package directory (default: lean-surfaces' .lake/packages inside it,
                    svGolf's own .lake/packages standalone)
  SVGOLF_PYTHON     interpreter for the extractor (default: python3.12)
  SVGOLF_POSTSYNTH_SALT  salt of the postsynth random vectors' seed (default
                    empty: reproducible by anyone; a competition sets a secret)
  SVGOLF_POSTSYNTH  `light` (default) or `full`: the post-synthesis mode;
                    `--postsynth` overrides it. Competition and verification
                    runs set `full`; the leaderboard's `add`/`verify` pass it
                    through (README.md, "Checking")

v0 LIMITS (README.md, "Checker v0 limits"): the sandbox needs a mechanism on the machine (without
one, `auto` runs the solution's Lean with the checker's privileges and says so); the parsers that run
IN the checker's own process (pyslang in the source gate, the banlist and fourstate front checks) are
not sandboxed; single-file submissions.

`bv_decide` is NOT SUPPORTED (decided 2026-11-01: "Let's not support external solvers for now"): it runs an
external SAT solver (`cadical`), which the solution's compile sandbox would have to be allowed to start
(`fork`, the exec of `cadical`, a writable temporary directory). `BV_DECIDE_SUPPORTED` below is False, so a
task's `allow_bv_decide: true` is an infrastructure error, the comparator is never given `--bv-decide`, and
the sandbox Spec never gets the solver; a submission that uses `bv_decide` is refused with a hint at
`solution` (sandbox on) or `comparator` (sandbox off). The groundwork stays in the tree, dormant: the
comparator's re-verification of the generated axiom (check/Comparator.lean, point 6) and the sandbox grant
(`Lean._run_sandboxed(bv_solver=...)`). README.md, "bv_decide", says what enabling it would take.
"""

import argparse
import ast
import hashlib
import importlib.util
import json
import os
import re
import shlex
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time

sys.dont_write_bytecode = True
SVGOLF = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(SVGOLF, "score"))
sys.path.insert(0, os.path.join(SVGOLF, "check"))
import banlist  # noqa: E402
import clocked_rules  # noqa: E402  (check/clocked_rules.py: txtask-v2's rules, Python twins before the proof)
import envelope  # noqa: E402  (check/envelope.py: the one extraction path)
import layout  # noqa: E402  (check/layout.py: where lean-surfaces is, in either layout)
import fourstate  # noqa: E402  (score/fourstate.py: no x or z value can arise at the probed points)
import postsynth  # noqa: E402  (check/postsynth.py: the post-synthesis check)
import sandbox  # noqa: E402  (check/sandbox/: the environment scrub, the sandbox, WP-S)
import ppa  # noqa: E402  (score/ppa.py: the sky130 PPA columns, A0' ranked, WP-X3)
import score  # noqa: E402
from envelope import parse_point, point_str, probe_points  # noqa: E402,F401

LS_ROOT = envelope.LS_ROOT
LAYOUT = envelope.LAYOUT      # "inside" lean-surfaces or "standalone" (check/layout.py)
EXTRACTOR = envelope.EXTRACTOR
ENVELOPE_PY = os.path.join(SVGOLF, "check", "envelope.py")
COMPARATOR = os.path.join(SVGOLF, "check", "Comparator.lean")
SVEVAL_SRC = os.path.join(SVGOLF, "check", "SvEval.lean")
# The limit of each of the comparator and leanchecker (they run no submission code, but a submission can make kernel
# checking slow), the default of task.json's `verify_time_limit_s`. Since 2026-11-06 it counts CPU SECONDS of the Lean
# process tree, as the solution's limit does, with a wall-clock BACKSTOP of VERIFY_WALL_FACTOR times it (`verify_limits`):
# a wall-clock limit let the machine's load reject an honest record when it was replayed.
VERIFY_TIME_LIMIT_S = 900
# The wall-clock limit of a sandboxed Lean run that has no task limit (the generated design module, the
# import probe, `--tactics`): they run no player proof, but they run on the player's design.
LEAN_DEFAULT_WALL_S = 900
# The `--ppa` modes (score/ppa.py columns: A0' is the ranked score; `off` leaves a result that cannot be ranked).
PPA_MODES = ("auto", "off", "require")

# `bv_decide` is NOT SUPPORTED. The tactic starts an EXTERNAL SAT solver (the toolchain's `cadical`) and reads
# its LRAT proof back, so the solution's compile would need `fork`, the exec of `cadical` and a writable
# temporary directory inside the sandbox (WP-BV measured that these three are the minimum). The maintainers declined
# that widening on 2026-11-01 ("maybe that's a bad idea. Let's not support external solvers for now"): the
# register policy (docs/sv-refusals.json) and README.md ("bv_decide") record the ruling. While this is False:
#   * `allow_bv_decide: true` in a task.json is an infrastructure error (absent or false: bv_decide is forbidden);
#   * the comparator is never given `--bv-decide`, so it rejects any bv_decide axiom;
#   * the sandbox Spec of the solution's compile NEVER gets `fork`, the exec of `cadical` or the private TMPDIR
#     (`Lean._run_sandboxed` checks this constant itself);
#   * a failed or rejected bv_decide proof carries a hint (`bv_decide_hint`).
# The dormant groundwork (the comparator's re-verification, check/Comparator.lean point 6, and the Spec grant) is
# kept, with its tests, so that enabling is a small change. NOTHING outside this file can switch it on: no
# environment variable, option or task key reads it. The tests that exercise the enabled path set it inside
# their own process (tests/checker/check_bv_enabled.py, a wrapper script; unittest patches).
BV_DECIDE_SUPPORTED = False
BV_DECIDE_HINT = ("bv_decide runs an external SAT solver (cadical), which the checker does not support; prove the "
                  "goal with decide +kernel, omega, simp or a symbolic argument (svgolf/README.md, \"bv_decide\")")

# The module roots of Mathlib's package closure (WP-B, 2026-10-31: Mathlib is allowed in
# submissions). They are the packages of lean-surfaces' `lake-manifest.json` that the module
# `Mathlib` reaches through its imports; the manifest also pins `Cli`, which only Mathlib's own
# `cache` executable uses, so it is not admitted. `tests/imports/test_allowlist.py` recomputes
# the import closure of `Mathlib` from the package sources and requires its roots to be exactly
# these. They are in svGolf's package directory (lean-surfaces' own when svGolf sits inside it,
# where svgolf/lakefile.toml's `packagesDir` points), so `lake env` already puts their build
# directories on LEAN_PATH: an admitted import resolves without any other change.
PACKAGE_ROOTS = ["Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "ImportGraph",
                 "LeanSearchClient"]

# Modules a solution may import. Everything else (Examples.*, LeanModels.Python.*, another
# submission, a lookalike such as `Mathlib2`) is rejected.
IMPORT_ALLOW = [
    r"Init(\..+)?", r"Std(\..+)?", r"Lean(\..+)?",
    r"LeanModels\.Sv(\..+)?", r"SvGolf(\..+)?", r"tasks(\..+)?",
    r"Submission\.Design",
] + [re.escape(r) + r"(\..+)?" for r in PACKAGE_ROOTS]


# A Lean failure that says nothing about the design: a build product that is
# missing or unreadable (a concurrent rebuild of LeanModels.Sv, say).
INFRA_LEAN = re.compile(r"object file .* does not exist|failed to open olean|"
                        r"failed to read file .*\.olean|could not find .*\.olean|"
                        r"unknown package|incompatible header", re.IGNORECASE)


class Reject(Exception):
    def __init__(self, stage, msg, **info):
        super().__init__(msg)
        self.stage, self.msg, self.info = stage, msg, info


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def tail(text, n=4000):
    return text if len(text) <= n else "..." + text[-n:]


# The first line of each Lean message that is an error: `<file>:<line>:<col>: error: ...`.
LEAN_ERROR_LINE = re.compile(r"^[^\n]*?:\d+:\d+: error\b[^\n]*", re.M)
# At most this many characters of one error line in the list `errors_first` puts in front.
ERROR_LINE_CAP = 300


def errors_first(text, n=4000):
    """Lean's output `text` for an error message, about `n` characters at most: the text itself when it fits;
    otherwise EVERY `file:line:col: error:` line first (the first line of each error, in order, each cut at
    ERROR_LINE_CAP, the list at half of `n`), then the tail of the output. A plain `tail` keeps the end, which is the
    goal dump of the LAST error, and cuts the first error, which is usually the one to fix."""
    if len(text) <= n:
        return text
    heads, used = [], 0
    found = [m.group(0) for m in LEAN_ERROR_LINE.finditer(text)]
    for ln in found:
        ln = ln if len(ln) <= ERROR_LINE_CAP else ln[:ERROR_LINE_CAP] + "..."
        if used + len(ln) + 1 > n // 2:
            break
        heads.append(ln)
        used += len(ln) + 1
    if not heads:
        return tail(text, n)
    more = len(found) - len(heads)
    head = (f"the errors ({len(found)}, the first line of each" + (f"; {more} more not listed" if more else "")
            + "):\n" + "\n".join(heads) + "\nthe end of Lean's output:\n")
    return head + tail(text, max(n - len(head), 200))


def log(*a):
    print(*a, file=sys.stderr, flush=True)


def stage_start(stage, detail="", wrap=()):
    """The one stderr line a long stage prints when it starts: `check: <stage> ...` (and what it runs; with a Lean
    wrapper, that the stage may queue behind it first)."""
    extra = [detail] if detail else []
    if wrap:
        extra.append("behind the Lean wrapper, which may queue it first")
    log(f"check: {stage} ..." + (f" ({'; '.join(extra)})" if extra else ""))


# ---------------------------------------------------------------------------
# a timed child process (the wall-clock and CPU limits exclude waiting for the wrapper)
# ---------------------------------------------------------------------------

def timed_main(argv):
    """`check.py --_timed WALL_S [limits] -- COMMAND...`: the supervisor (check/sandbox/supervisor.py), which
    enforces the wall-clock limit and, with `--cpu-limit-s`, the CPU limit of the command's process tree (both
    excluding the wait in a slot wrapper in front of it) and, for a sandboxed command, the memory, output and
    file-size limits, from OUTSIDE the sandbox."""
    return sandbox.supervisor.main(argv)


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

# The line the supervisor prints on stderr when its command ends (see Lean.run):
# `SVGOLF_ELAPSED <s> cpu_s=<cpu s> peak_rss_mb=<n> out_bytes=<n> verdict=<none|memory|output>`.
ELAPSED_LINE = re.compile(r"SVGOLF_ELAPSED ([\d.]+)([^\n]*)\n?")


def control_fields(text):
    """The `key=value` fields of the rest of a supervisor control line."""
    return dict(kv.split("=", 1) for kv in text.split() if "=" in kv)


def timeout_status(out):
    """(wall seconds, fields) of the supervisor's LAST timeout line in `out` (`SVGOLF_TIMEOUT after <s>s cpu_s=<cpu s>
    by=<wall|cpu>`; a line without fields is an older supervisor's, stopped by the wall clock), or None."""
    ms = TIMEOUT_LINE.findall(out)
    if not ms:
        return None
    return float(ms[-1][0]), control_fields(ms[-1][1])


def split_status(out):
    """(`out` without the supervisor's lines, the elapsed seconds or None, the genuine line's
    `key=value` fields). The genuine reading is the LAST line (the supervisor prints it after the
    command has ended), so a solution that prints the same words cannot forge it; none of these
    lines ever reaches an error message or the result JSON."""
    ms = ELAPSED_LINE.findall(out)
    fields = control_fields(ms[-1][1]) if ms else {}
    return ELAPSED_LINE.sub("", out), float(ms[-1][0]) if ms else None, fields


def stopped_elapsed(rc, out, wall, elapsed):
    """`elapsed`, or, for a command the supervisor stopped (status 124, its `SVGOLF_TIMEOUT` line in `out`): at its
    wall-clock limit, `wall` (the supervisor stops it within one poll, 0.1 s, of the limit, so the run took the limit
    and the rest of the call was the wait in front of it); at its CPU limit (`by=cpu`), the wall seconds the line
    reports."""
    t = timeout_status(out) if elapsed is None and rc == 124 else None
    if t is None:
        return elapsed
    run_s, fields = t
    if fields.get("by") == "cpu" or not wall:
        return run_s
    return float(wall)


def run_usage(rc, out, fields, elapsed):
    """What the supervisor measured of one command: {"wall_s": wall seconds, "cpu_s": CPU seconds of its process
    tree (None when the line carries none), "stopped_by": "cpu" | "wall" for a command stopped at a limit (status
    124), else None}. `out` still holds a timeout line; `fields` are the elapsed line's (`split_status`)."""
    t = timeout_status(out) if rc == 124 else None
    if t is not None:
        f = t[1]
        cpu = f.get("cpu_s")
        return {"wall_s": elapsed, "cpu_s": float(cpu) if cpu else None, "stopped_by": f.get("by", "wall")}
    cpu = fields.get("cpu_s")
    return {"wall_s": elapsed, "cpu_s": float(cpu) if cpu else None, "stopped_by": None}


def split_elapsed(out):
    """(`out` without the supervisor's lines, the elapsed seconds or None): `split_status` without
    the fields."""
    clean, elapsed, _ = split_status(out)
    return clean, elapsed


# ---------------------------------------------------------------------------
# the solution's progress: which declarations the kernel finished, and when
# ---------------------------------------------------------------------------

# The solution's compile runs with Lean's trace class `Kernel` on (`PROGRESS_OPTION`): Lean prints one line as the
# kernel finishes each declaration (auxiliary ones included), in the order of the file,
#     [Kernel] ✅️ typechecking declarations [Submission.band_interface]
# and the supervisor gives Lean a pseudo-terminal as its stdout (`--pty`), so that each line arrives when Lean prints it.
# Through a pipe, Lean's stdout is block-buffered and a compile stopped at its limit loses every message it printed
# (measured 2026-11-05: not one line of four finished declarations arrived before the kill). The checker notes when each
# line arrives (`run_stamped`), removes the lines from the messages it keeps (`strip_progress`), and on a timeout says
# which declaration finished last and when (`progress_summary`, `progress_sentence`, `log_solution_time`).
#
# The trace is a message, so the proof can see it: a `#guard_msgs` around a declaration would find one message more and
# fail a proof that compiles without it. A failed compile whose output mentions the trace anywhere but in its own lines
# (`progress_leaked`) is therefore compiled once more WITHOUT the option, and that compile's verdict stands.
PROGRESS_OPTION = "-Dtrace.Kernel=true"
PROGRESS_LINE = re.compile(r"^\[Kernel\] (?:\S+ )?typechecking declarations \[(.*)\]\r?$")
PROGRESS_LINES = re.compile(r"^\[Kernel\] (?:\S+ )?typechecking declarations \[.*\]\r?\n?", re.M)
TIMEOUT_LINE = re.compile(r"SVGOLF_TIMEOUT after ([\d.]+)s([^\n]*)")
# how many of the longest gaps between finished declarations `progress_summary` keeps
PROGRESS_SLOWEST = 3


def strip_progress(text):
    """`text` without the progress lines (`PROGRESS_LINE`)."""
    return PROGRESS_LINES.sub("", text)


def progress_leaked(text):
    """Whether the progress trace shows in `text` outside its own lines (a `#guard_msgs` that saw it, say)."""
    return "[Kernel]" in strip_progress(text)


def run_stamped(cmd, cwd, env):
    """`subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, errors="replace")`, which also notes
    when each line of either stream arrived: (the CompletedProcess, [(seconds after the call began, "out" | "err",
    line)] in the order of arrival)."""
    t0 = time.time()
    p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    raw, stamps, lock = {"out": [], "err": []}, [], threading.Lock()

    def pump(name, fh):
        for line in iter(fh.readline, b""):
            t = time.time() - t0
            with lock:
                raw[name].append(line)
                stamps.append((t, name, line.decode("utf-8", errors="replace")))
    threads = [threading.Thread(target=pump, args=(n, f), daemon=True) for n, f in (("out", p.stdout), ("err", p.stderr))]
    for th in threads:
        th.start()
    for th in threads:
        th.join()
    p.stdout.close()
    p.stderr.close()
    p.wait()
    text = {n: b"".join(v).decode("utf-8", errors="replace") for n, v in raw.items()}
    return subprocess.CompletedProcess(cmd, p.returncode, text["out"], text["err"]), stamps


def own_name(decls):
    """The first name of a progress line's `decls` with a private name's prefix (`_private.<module>.0.`) removed."""
    first = decls.split(", ")[0]
    if first.startswith("_private.") and ".0." in first:
        first = first.split(".0.", 1)[1]
    return first


def is_auxiliary(decls):
    """Whether a progress line is for an AUXILIARY declaration: a name with a component that starts with `_` (the
    temporary definitions a tactic evaluates, `_tmp._@...`; abstracted proofs, `Submission.foo._proof_1`). Lean
    checks those while it elaborates the declaration they serve, and prints them first."""
    return any(c.startswith("_") for c in own_name(decls).split("."))


def progress_summary(stamps, rc, timeout):
    """What the progress lines among `stamps` (`run_stamped`) say, or None when there is none to read. A declaration's
    wait is the time since the line before it, or since the start for the first (the imports included); an auxiliary
    declaration's line (`is_auxiliary`) belongs to the declaration whose line follows it, so its wait is added to that
    one's. Keys: `finished` and `auxiliary`, the counts of the two kinds of line; `last`, the last declaration that
    finished ({"decls": the names Lean printed, "at_s": when its line arrived}; the last auxiliary line when there is
    no other); `slowest`, the longest waits ({"decls", "s"}, and `first` for the first declaration, whose wait includes
    the imports), at most PROGRESS_SLOWEST, longest first; `run_s`, how
    long the command ran. Times are wall-clock seconds since the command STARTED (the wait in a Lean wrapper in
    front of it excluded), DERIVED from when the supervisor's control line arrived: it ends a run of `run_s` seconds,
    on a timeout (`rc` 124) the wall-clock limit `timeout`, or for a run stopped at its CPU limit (`by=cpu`) the wall
    seconds the line reports."""
    run_s = anchor = None
    for t, name, line in stamps:
        if name != "err":
            continue
        m = TIMEOUT_LINE.search(line) if rc == 124 else ELAPSED_LINE.search(line)
        if m:
            by_cpu = rc == 124 and control_fields(m.group(2)).get("by") == "cpu"
            run_s = float(timeout) if rc == 124 and timeout and not by_cpu else float(m.group(1))
            anchor = t - run_s
    if anchor is None:
        return None
    rows, prev, pending, aux, last_aux = [], 0.0, 0.0, 0, None
    for t, name, line in stamps:
        m = PROGRESS_LINE.match(line.rstrip("\n")) if name == "out" else None
        if not m:
            continue
        at = round(min(max(t - anchor, 0.0), run_s), 2)
        wait, prev = max(at - prev, 0.0), at
        if is_auxiliary(m.group(1)):
            aux, pending, last_aux = aux + 1, pending + wait, {"decls": m.group(1), "at_s": at}
            continue
        rows.append({"decls": m.group(1), "at_s": at, "s": round(pending + wait, 2)})
        pending = 0.0
    if rows:
        rows[0]["first"] = True           # its wait includes the imports
    slowest = sorted(rows, key=lambda r: -r["s"])[:PROGRESS_SLOWEST]
    last = {k: rows[-1][k] for k in ("decls", "at_s")} if rows else last_aux
    return {"finished": len(rows), "auxiliary": aux, "run_s": round(run_s, 2), "last": last,
            "slowest": [{k: r[k] for k in ("decls", "s", "first") if k in r} for r in slowest]}


class Lean:
    """Runs `lake` and `lean` for one staging tree.

    Without the sandbox every call is `lake env <cmd>` (the old path, with a scrubbed environment). With it,
    the commands that run SUBMITTED TEXT (`lean` compiles, the comparator, `leanchecker`) go through
    `_run_sandboxed`: `lake env` is asked ONCE, outside the sandbox (lake runs `git` in every package
    checkout and would clone a missing one: it cannot be inside), and the toolchain's `lean`/`leanchecker`
    then run DIRECTLY under a Spec: reads of the toolchain, the Lean search path and the staging tree;
    writes of one fresh output directory (the checker adopts `Solution.olean` from it); no network, no
    other program, a scrubbed environment, the supervisor's limits."""

    def __init__(self, stage_dir, wrap):
        self.stage = stage_dir
        self.build = os.path.join(stage_dir, "build")
        self.wrap = wrap
        self._lake_env = None          # (search path entries, toolchain sysroot), from `lake env`
        self._waited = 0.0             # seconds spent behind the wrapper since the last `take_wait`
        self.progress = None           # `progress_summary` of the last call with `progress`, or None
        self.usage = None              # `run_usage` of the last supervised call (wall and CPU seconds), or None

    def _need_lake(self):
        """An infrastructure error that says what to do, not a traceback, when there is no `lake` to run (behind a
        wrapper the wrapper finds it)."""
        if not self.wrap and not shutil.which("lake"):
            raise RuntimeError("`lake` is not on PATH (infrastructure): install elan, which installs the Lean "
                               "toolchain that lean-toolchain pins, then " + envelope.BUILD_FIRST)

    def _supervised(self, cmd):
        """`cmd` under the supervisor, with no limit, when a wrapper is in front of it: the supervisor's elapsed time
        starts when the command does, so the wait in the wrapper can be told apart from the run (`take_wait`)."""
        if not self.wrap:
            return cmd
        return [sys.executable, "-S", "-B", sandbox.SUPERVISOR, "0", "--nofile", "0", "--"] + cmd

    def _note_wait(self, total, elapsed):
        """Account the part of a wrapped call's `total` seconds before its command started (`elapsed`: the
        supervisor's reading of the command alone)."""
        if self.wrap and elapsed is not None:
            self._waited += max(0.0, total - elapsed)

    def take_wait(self):
        """The seconds the calls since the last `take_wait` spent before their command started (the wrapper's queue,
        and the supervisor's start-up, a fraction of a second), and reset; None without a wrapper (nothing waits)."""
        if not self.wrap:
            return None
        w, self._waited = round(self._waited, 2), 0.0
        return w

    def _env(self):
        env = sandbox.scrubbed_env()
        env["LEAN_PATH"] = self.build + (":" + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
        return env

    def _capture_lake_env(self):
        """(search path, sysroot) from `lake env` (LEAN_PATH, LEAN_SYSROOT), once, unsandboxed."""
        if self._lake_env is None:
            # (`printenv` takes one name on macOS: ask a shell for both)
            self._need_lake()
            t0 = time.time()
            proc = subprocess.run(self.wrap + self._supervised(
                ["lake", "env", "sh", "-c", 'printf "%s\\n%s\\n" "$LEAN_PATH" "$LEAN_SYSROOT"']),
                cwd=SVGOLF, env=self._env(), capture_output=True, text=True)
            err, elapsed = split_elapsed(proc.stderr)
            self._note_wait(time.time() - t0, elapsed)
            lines = [ln.strip() for ln in (proc.stdout).splitlines() if ln.strip()]
            if proc.returncode != 0 or len(lines) < 2 or not os.path.isdir(lines[-1]):
                raise RuntimeError("`lake env` gave no LEAN_PATH or LEAN_SYSROOT "
                                   f"(infrastructure; exit {proc.returncode}; is the project built? "
                                   f"{envelope.BUILD_FIRST}):\n{tail(proc.stdout + err)}")
            self._lake_env = ([p for p in lines[-2].split(":") if p], lines[-1])
        return self._lake_env

    def run(self, args, timeout=None, lake_env=True, bv_solver=False, progress=False, cpu_limit=None):
        """(exit status, output, wall seconds). `timeout`: the wall-clock limit; `cpu_limit` (with a `timeout`, then
        the wall-clock BACKSTOP): a limit on the CPU seconds of the command's process tree (the supervisor's
        `--cpu-limit-s`). `self.usage` is set (`run_usage`: wall and CPU seconds, which limit stopped it). `progress`
        (a timed call): the command's stdout is a pseudo-terminal (the supervisor's `--pty`), every line's arrival is
        noted, and `self.progress` is set (`progress_summary`)."""
        pol = sandbox.policy()
        self.progress = None
        self.usage = None
        if pol.active and lake_env:
            if args[:2] == ["printenv", "LEAN_PATH"]:
                t0 = time.time()
                path, _ = self._capture_lake_env()
                return 0, ":".join(path) + "\n", round(time.time() - t0, 2)
            if args[0] in ("lean", "leanchecker"):
                return self._run_sandboxed(args, timeout, bv_solver, progress, cpu_limit)
        if pol.active:
            pol.unsandboxed("lake build (trusted modules only)" if not lake_env else "lake env " + args[0])
        # an ALLOWLISTED environment (check/sandbox/envscrub.py): the competition salt and the
        # checker's other secrets never reach a process that runs the submission's Lean
        env = self._env()
        self._need_lake()
        inner = (["lake", "env"] if lake_env else ["lake"]) + args
        progress = bool(progress and timeout)
        if timeout:
            inner = ([sys.executable, os.path.abspath(__file__), "--_timed", str(timeout)]
                     + (["--cpu-limit-s", str(cpu_limit)] if cpu_limit else [])
                     + (["--pty"] if progress else []) + ["--"] + inner)
        else:
            inner = self._supervised(inner)       # (a wrapper: the untimed `lake build` too, B7)
        t0 = time.time()
        if progress:
            proc, stamps = run_stamped(self.wrap + inner, SVGOLF, env)
            self.progress = progress_summary(stamps, proc.returncode, timeout)
        else:
            proc = subprocess.run(self.wrap + inner, cwd=SVGOLF, env=env, capture_output=True,
                                  text=True)
        out = proc.stdout + proc.stderr
        # the elapsed-time line is parsed here and removed from the text
        out, elapsed, fields = split_status(out)
        elapsed = stopped_elapsed(proc.returncode, out, timeout, elapsed)
        total = time.time() - t0
        self._note_wait(total, elapsed)
        wall = round(total, 2) if elapsed is None else elapsed
        self.usage = run_usage(proc.returncode, out, fields, wall)
        return proc.returncode, out, wall

    def _run_sandboxed(self, args, timeout, bv_solver=False, progress=False, cpu_limit=None):
        """`bv_solver` (DORMANT: honoured only while `BV_DECIDE_SUPPORTED`, which is False; the solution's compile
        of a task that allows `bv_decide`, and nothing else): the
        tactic starts the toolchain's `cadical` (a CNF file and an LRAT proof file in the temporary
        directory) and reads its proof back. So that one program is added to the spec, with the right
        to start it (`fork`), and one fresh directory to write, which is the process's TMPDIR. The
        program is the toolchain's own binary, it runs under the same profile (no network, no other
        program, no read outside the inputs, the same supervisor limits for the whole process group),
        and a hostile file that starts it with other arguments gets no capability it did not have:
        it can read what the profile lets Lean read and write the one temporary directory."""
        pol = sandbox.policy()
        search, sysroot = self._capture_lake_env()
        exe = os.path.join(sysroot, "bin", args[0])
        targs = list(args[1:])
        outdir = adopt = None
        if "-o" in targs:           # the compile writes its .olean into a FRESH directory, which the checker then reads
            i = targs.index("-o")
            target = targs[i + 1]
            outdir = pol.mkdtemp("out-")
            targs[i + 1] = os.path.join(outdir, os.path.basename(target))
            adopt = (targs[i + 1], target)
        read = [sysroot] + [p for p in search if os.path.exists(p)] + [self.stage]
        read += [a for a in targs if a.endswith(".lean") and os.path.isfile(a)]   # check/Comparator.lean
        kind = args[0] + (" --run" if "--run" in args else "") + (" -o" if outdir else "")
        env = {"PATH": "/usr/bin:/bin", "HOME": "/var/empty", "LC_ALL": "en_US.UTF-8" if sys.platform == "darwin"
               else "C.UTF-8", "LEAN_PATH": ":".join(search), "LEAN_SYSROOT": sysroot}
        execs, write, fork = [exe], [outdir] if outdir else [], False
        solver = os.path.join(sysroot, "bin", "cadical")
        if bv_solver and BV_DECIDE_SUPPORTED and os.path.isfile(solver):
            tmp = pol.mkdtemp("tmp-")
            execs.append(solver)
            write.append(tmp)
            fork = True
            env["TMPDIR"] = os.path.realpath(tmp)
            kind += " +cadical"
        spec = sandbox.Spec(exec_paths=execs, map_exec=[sysroot], read=read, write=write, fork=fork,
                            label="lean: " + kind)
        wall = timeout or LEAN_DEFAULT_WALL_S
        lim = sandbox.limits(wall, "lean")
        argv = pol.command(spec, [exe] + targs, env, self.stage)
        sup = [sys.executable, "-S", "-B", sandbox.SUPERVISOR, str(wall)] + (
               ["--cpu-limit-s", str(cpu_limit)] if cpu_limit else []) + ["--rss-mb", str(lim["rss_mb"]),
               "--out-mb", str(lim["out_mb"]), "--fsize-mb", str(lim["fsize_mb"]), "--cpu-s", str(lim["cpu_s"]),
               "--merge"] + (["--pty"] if progress else []) + [
               "--cwd", self.stage, "--forward-env", "LEAN_NUM_THREADS", "--"] + argv   # the slot's thread budget
        t0 = time.time()
        if progress:
            proc, stamps = run_stamped(self.wrap + sup, SVGOLF, sandbox.scrubbed_env())
            self.progress = progress_summary(stamps, proc.returncode, wall)
        else:
            proc = subprocess.run(self.wrap + sup, cwd=SVGOLF, env=sandbox.scrubbed_env(), capture_output=True,
                                  text=True, errors="replace")
        out, elapsed, fields = split_status(proc.stdout + proc.stderr)
        elapsed = stopped_elapsed(proc.returncode, out, wall, elapsed)
        total = time.time() - t0
        self._note_wait(total, elapsed)
        if fields.get("peak_rss_mb"):
            pol.note["peak_rss_mb"] = max(pol.note.get("peak_rss_mb", 0), int(fields["peak_rss_mb"]))
        if adopt:
            self._adopt_output(*adopt, outdir)
        el = round(total, 2) if elapsed is None else elapsed
        self.usage = run_usage(proc.returncode, out, fields, el)
        return proc.returncode, out, el

    def _adopt_output(self, produced, target, outdir):
        """The compile's `.olean`, from the sandbox's output directory into the staging tree: a regular file,
        copied by the checker (never a link, never anything else the process left there)."""
        pol = sandbox.policy()
        name = os.path.basename(produced)
        for e in sorted(os.listdir(outdir)):
            if e != name:
                pol.note["stray_outputs"].append(e[:80])
        try:
            st = os.lstat(produced)
        except FileNotFoundError:
            return
        if not stat.S_ISREG(st.st_mode):
            pol.note["stray_outputs"].append(f"{name} (not a regular file)")
            return
        os.makedirs(os.path.dirname(target), exist_ok=True)
        tmp = target + ".adopting"
        shutil.copyfile(produced, tmp)
        os.replace(tmp, target)

    def compile(self, module_path, timeout=None, bv_solver=False, progress=False, cpu_limit=None):
        """`progress` (with a `timeout`): compile with `PROGRESS_OPTION` and note when each declaration finished
        (`self.progress`); the progress lines stay in the output (`strip_progress` removes them). `cpu_limit`: as
        for `run` (`timeout` is then the wall-clock backstop)."""
        rel = os.path.relpath(module_path, self.stage)
        olean = os.path.join(self.build, os.path.splitext(rel)[0] + ".olean")
        os.makedirs(os.path.dirname(olean), exist_ok=True)
        progress = bool(progress and timeout)
        return self.run(["lean", "-R", self.stage, "-o", olean] + ([PROGRESS_OPTION] if progress else [])
                        + [module_path], timeout=timeout, bv_solver=bv_solver, progress=progress,
                        cpu_limit=cpu_limit)


def note_wait(rec, lean):
    """`rec["waited"]` (a stage's record): the seconds its Lean calls, and any helper call since the previous stage
    (the search-path query), spent behind the slot wrapper before their command started. Only with a wrapper (and a
    runner that tracks it): the stage's `seconds` never include the wait, and without a wrapper nothing waits."""
    w = lean.take_wait() if hasattr(lean, "take_wait") else None
    if w is not None:
        rec["waited"] = round(rec.get("waited", 0) + w, 2)


# The solution stage's limit, the task's `time_limit_s`, counts the CPU seconds of the Lean process tree (user + system,
# every thread; decided 2026-11-05), so a loaded machine does not push a proof over it, and the wait for a Lean wrapper
# never counts. A proof that waits instead of computing (a `sleep`, a blocked read) uses no CPU, so the compile also has
# a WALL-CLOCK BACKSTOP of SOLUTION_WALL_FACTOR times the limit (1500 s for the 300 s limit). Why 5: an honest proof's
# wall clock runs past its CPU time only while it waits for the machine, and the worst ratio measured is about 4 (README
# "Mathlib in submissions": `add_n` with `Mathlib.Tactic` took 82 to 94 s of wall clock for 23.7 s of CPU while other jobs
# had the machine swapping), so 5 times stops a proof that sleeps or blocks within 10 minutes and leaves an honest one
# on a loaded machine room to finish.
SOLUTION_WALL_FACTOR = 5


def solution_wall_backstop(limit):
    """The wall-clock backstop of a solution compile under the CPU limit `limit` (s): SOLUTION_WALL_FACTOR x it."""
    return SOLUTION_WALL_FACTOR * limit


# The comparator and leanchecker (the replay of the compiled modules) count CPU seconds too (since 2026-11-06), with the
# backstop factor of the solution's limit, for the same reason: their wall clock runs past their CPU time only while they
# wait, for the machine or for a read.
VERIFY_WALL_FACTOR = SOLUTION_WALL_FACTOR


def verify_limits(vlimit):
    """(CPU limit, wall-clock backstop) of each of the comparator and leanchecker under `verify_time_limit_s` = `vlimit`."""
    return vlimit, VERIFY_WALL_FACTOR * vlimit


def verify_record(rc, el, vlimit, wall_limit, usage):
    """The stage record of a comparator or leanchecker run: its exit status, wall seconds, CPU seconds (`usage`, the
    runner's `run_usage`), the limit and what it counts, the backstop, and on a timeout (status 124) which one stopped it."""
    usage = usage or {}
    rec = {"exit": rc, "seconds": el, "cpu_seconds": usage.get("cpu_s"), "time_limit_s": vlimit,
           "time_limit_counts": "cpu", "wall_limit_s": wall_limit}
    if rc == 124:
        rec["stopped_by"] = usage.get("stopped_by") or "wall"
    return rec


# Over this fraction of the task's CPU limit the solution stage warns (CPU time does not follow the machine's load,
# but a slower machine needs more of it).
SOLUTION_WARN_FRACTION = 0.5


def decl_name(decls):
    """A declaration as `progress_summary` read it (the names Lean printed, `a, b` for a mutual block), for a
    sentence: in backticks, a private one by its own name; an auxiliary one (`is_auxiliary`) with the declaration
    it belongs to when its name says (`Submission.foo._proof_1`), else as an auxiliary declaration."""
    own = own_name(decls)
    parts = own.split(".")
    aux = next((i for i, c in enumerate(parts) if c.startswith("_")), None)
    if aux is None:
        return f"`{own}`" + (f" (with `{decls.split(', ', 1)[1]}`)" if ", " in decls else "")
    if aux == 0:
        return "an auxiliary declaration"
    return f"`{own}` (an auxiliary of `{'.'.join(parts[:aux])}`)"


def slowest_text(progress):
    """The longest waits of `progress` for a finished declaration, as one clause, or ""."""
    rows = [r for r in (progress or {}).get("slowest") or [] if r["s"] >= 0.05]
    return ", ".join(f"{decl_name(r['decls'])} {r['s']:.1f} s" + (" (the imports included)" if r.get("first") else "")
                     for r in rows)


def progress_sentence(progress):
    """Where the time of a compile stopped at its limit went, from `progress` (`progress_summary`): one sentence,
    or "" when the compile reported none."""
    if not progress:
        return ""
    run_s, last = progress["run_s"], progress["last"]
    n, aux = progress["finished"], progress.get("auxiliary", 0)
    if not last or not n:
        return (f"no declaration finished in the {run_s:.1f} s" + (f" ({aux} auxiliary ones did)" if aux else "")
                + ": they went to the imports and to the first declaration of the file")
    return (f"{n} declaration{'s' if n != 1 else ''} finished" + (f" (and {aux} auxiliary ones)" if aux else "")
            + f", the last {decl_name(last['decls'])} {last['at_s']:.1f} s into the run; the "
            f"{max(run_s - last['at_s'], 0.0):.1f} s after it went to what follows it in the file, which had not finished")


def cpu_text(cpu):
    """CPU seconds for a sentence: `12.3 CPU s`, or `an unmeasured amount of CPU time`."""
    return f"{cpu:.1f} CPU s" if cpu is not None else "an unmeasured amount of CPU time"


def solution_timeout_text(limit, wall_limit, el, cpu, stopped_by, who="Lean"):
    """Why a solution compile (or, `who` naming it, a comparator or leanchecker run) was stopped (status 124), as the
    clause after "did not finish within": at the CPU limit `limit` (`stopped_by` "cpu") or at the wall-clock backstop
    `wall_limit` ("wall")."""
    if stopped_by == "cpu":
        return f"the {limit:g} s CPU limit: {who} used {cpu_text(cpu)} in {el:.1f} s of wall clock and was stopped"
    return (f"the {wall_limit or el:g} s wall-clock backstop: {who} used {cpu_text(cpu)} of its {limit:g} s CPU limit in "
            f"{el:.1f} s and was stopped, so it waited (a `sleep`, blocked I/O, a machine too loaded to run it)")


def log_solution_time(el, limit, waited, rc, progress=None, cpu=None, wall_limit=None, stopped_by=None):
    """The solution stage's lines on stderr: its CPU seconds (`cpu`) against the task's CPU limit, with the wall clock
    `el` apart (and the wait for the Lean wrapper, if any, which is never counted), and a warning past half the limit; on
    a timeout, which limit stopped it (`stopped_by`: the CPU limit, or the wall-clock backstop `wall_limit`) and where the
    time went (`progress`, `progress_sentence`), and with the warning, the declarations that took longest."""
    wait = f"; it waited {waited:.1f} s for the Lean wrapper first, not counted" if waited else ""
    if rc == 124:
        log("solution: did not finish within " + solution_timeout_text(limit, wall_limit, el, cpu, stopped_by) + wait)
        where = progress_sentence(progress)
        if where:
            log(f"solution: where the time went: {where}")
        slow = slowest_text(progress)
        if slow and (progress or {}).get("last"):
            log(f"solution: the longest waits for a declaration that finished: {slow}")
        return
    if not limit:
        return
    if cpu is None:
        log(f"solution: Lean ran {el:.1f} s of wall clock; its CPU time was not measured (the task's limit: "
            f"{limit:g} CPU s)" + wait)
        return
    log(f"solution: Lean used {cpu:.1f} CPU s of the task's {limit:g} s CPU limit ({100 * cpu / limit:.0f}%), in "
        f"{el:.1f} s of wall clock" + wait)
    if cpu > SOLUTION_WARN_FRACTION * limit:
        slow = slowest_text(progress)
        log(f"solution: WARNING: the proof used over half of the {limit:g} s CPU limit; CPU time does not follow the "
            "machine's load, but a slower machine needs more of it: make it faster"
            + (f" (the longest waits for a declaration: {slow})" if slow else ""))


def strip_lean_comments(text, keep_lines=False):
    """`text` with every comment replaced by whitespace, as Lean reads it: a block comment is a
    SEPARATOR (`import A/-c-/import B` is two imports; deleting the comment outright spliced the
    two tokens into one module name `Aimport` and hid the second import from the allowlist and
    from every import-dependent stage: WP-B review). `keep_lines`: the newlines inside a block
    comment stay, so that line N of the result is line N of `text` (Lean's error positions)."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            if depth == 0:
                out.append(" ")
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if keep_lines and text[i] == "\n":
                out.append("\n")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


_LEAN_ERROR_AT = re.compile(r"Solution\.lean:(\d+):\d+: error")
_SOLVER_TRACES = re.compile(r"cadical|external prover|external process|external solver|SAT solver", re.I)


def bv_decide_hint(source, output):
    """`BV_DECIDE_HINT` when a failed compile of the solution (`source`, the Lean text; `output`, Lean's messages)
    is the sandbox or a missing solver refusing `bv_decide`, else None. The sandbox's refusal is opaque: the
    tactic's first failure is `operation not permitted` (no writable temporary directory, then no fork, then no
    exec of `cadical`), with the position of the `bv_decide` token and no mention of the tactic or the solver.
    So the hint needs the file to use the tactic in code (a comment does not count) AND either a Lean error
    whose line is a line that mentions `bv_decide`, or a message that names the solver."""
    code = strip_lean_comments(source, keep_lines=True)
    if not re.search(r"\bbv_decide\b", code):
        return None
    lines = code.splitlines()
    for m in _LEAN_ERROR_AT.finditer(output):
        i = int(m.group(1)) - 1
        if 0 <= i < len(lines) and re.search(r"\bbv_decide\b", lines[i]):
            return BV_DECIDE_HINT
    return BV_DECIDE_HINT if _SOLVER_TRACES.search(output) else None


def parse_header(text):
    """The modules a Lean file imports, from its header (comments stripped)."""
    toks = strip_lean_comments(text).split()
    imports, i = [], 0
    if toks[:1] == ["module"] or toks[:1] == ["prelude"]:
        raise Reject("imports", f"`{toks[0]}` headers are not accepted in v0")
    while i < len(toks):
        t = toks[i]
        if t in ("public", "meta", "private") and i + 1 < len(toks) and toks[i + 1] == "import":
            i += 1
            continue
        if t != "import":
            break
        if i + 1 >= len(toks):
            raise Reject("imports", "dangling `import`")
        mod = toks[i + 1]
        if mod == "all" and i + 2 < len(toks):
            mod = toks[i + 2]
            i += 1
        imports.append(mod)
        i += 2
    return imports


def import_mismatch(parsed, recorded):
    """None if the direct imports the compiled `Submission.Solution` recorded (`recorded`, from the
    comparator: what Lean itself read from the header) are exactly the ones `parse_header` found
    (`parsed`; `Init` is implicit, and both sides are sets) and all of them are on the allowlist;
    otherwise the message. A solution whose header the Python reader and Lean read differently
    (a comment between two imports used to splice them into one token) is not trusted to have
    passed the allowlist, the package probe or the build of the imported LeanModels.Sv modules,
    which all work from `parsed`."""
    if recorded is None:
        raise RuntimeError("the comparator did not report the solution's imports (infrastructure)")
    rec = sorted(set(recorded) - {"Init"})
    par = sorted(set(parsed) - {"Init"})
    bad = [m for m in rec if not any(re.fullmatch(p, m) for p in IMPORT_ALLOW)]
    if bad:
        return f"the compiled solution imports modules outside the allowlist: {bad}"
    if rec != par:
        return (f"the header was read differently by the checker ({par}) and by Lean ({rec}); "
                "write each `import` on its own line")
    return None


def lean_string(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


# ---------------------------------------------------------------------------
# imports from packages (Mathlib and friends, WP-B)
# ---------------------------------------------------------------------------

# A module name the generated import probe may carry (no quoting, no punctuation).
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*")
# The two ways Lean says a module has no build product on the search path.
MISSING_OBJECT = re.compile(r"object file '[^']*' of module (\S+) does not exist")
UNKNOWN_PREFIX = re.compile(r"unknown module prefix '([^']*)'")


def package_imports(imports):
    """The imports whose root is one of PACKAGE_ROOTS (a package of the package directory)."""
    return [m for m in imports if m.split(".")[0] in PACKAGE_ROOTS]


def import_probe_text(pkg):
    """The generated `Submission.ImportProbe`: exactly the solution's package imports and
    nothing else. Trusted text (names checked against MODULE_NAME): when it fails, the
    failure is the machine's or a wrong module name, never the player's code, which is what
    lets the checker tell an infrastructure error from a rejection BEFORE the player's file
    compiles (a player's own output could forge any message the solution stage prints)."""
    # a line comment, not a `/-! -/` doc comment: that one is a command, and `import` must
    # come before every command
    return ("-- GENERATED by svgolf/check.py: the solution's package imports, compiled alone "
            "(WP-B). Not part of any submission.\n"
            + "".join(f"import {m}\n" for m in sorted(set(pkg))))


def packages_dir():
    """The package directory: `LS_ROOT/.lake/packages` inside lean-surfaces (where svgolf's
    lakefile points `packagesDir`), svGolf's own `.lake/packages` standalone, or SVGOLF_PACKAGES."""
    return layout.packages_dir(LAYOUT, SVGOLF, LS_ROOT)


def manifest_path():
    """The `lake-manifest.json` that pins the packages: lean-surfaces' inside it, svGolf's own
    (the root manifest) standalone."""
    return layout.manifest_path(LAYOUT, SVGOLF, LS_ROOT)


def package_dirs():
    """The package checkouts of the package directory: name -> directory."""
    pk = packages_dir()
    if not os.path.isdir(pk):
        return {}
    return {d: os.path.join(pk, d) for d in sorted(os.listdir(pk))
            if os.path.isdir(os.path.join(pk, d))}


def package_source_exists(module):
    """True if some package checkout has the SOURCE file of `module` (`Mathlib.Tactic.Ring` ->
    `<pkg>/Mathlib/Tactic/Ring.lean`): the module exists, whether or not this machine built it."""
    rel = os.path.join(*module.split(".")) + ".lean"
    return any(os.path.isfile(os.path.join(d, rel)) for d in package_dirs().values())


def classify_import_probe(pkg, rc, out, source_exists=None, search_path=()):
    """None if the probe compiled. Otherwise `("reject", message)`: a module the player named
    has NO source in the packages, so the name is stale or misspelled (`Mathlib.Data.Nat.Defs`,
    renamed away); or `("infra", message)`: everything that depends on this machine and not on
    the submission, i.e. a package whose build products are missing from the search path, a
    module a package HAS the source of but this machine did not build (`Batteries`, the
    umbrella, on a partial build: the verdict must not depend on which machine ran it), a module
    only a TRANSITIVE import needs (the `Mathlib` umbrella needs 110 Batteries modules that a
    partial build may lack), an incompatible or unreadable olean (`out` may then be empty: the
    exit status and the search path are in the message)."""
    if rc == 0:
        return None
    source_exists = source_exists or package_source_exists
    direct = set(pkg)
    missing = MISSING_OBJECT.findall(out)
    named = sorted(m for m in set(missing) if m in direct)
    if named and not any(source_exists(m) for m in named):
        return ("reject", f"no such module in the installed packages: {named} (a stale or "
                "misspelled module name: no package has a source file for it)")
    if missing or UNKNOWN_PREFIX.search(out):
        built = (f" ({named} exist in the packages' sources but are not built on this machine)"
                 if named else "")
        return ("infra", "the build products of a package the solution imports are missing "
                f"on this machine{built} (infrastructure, not a verdict on the submission): "
                + tail(out))
    where = [p for p in search_path if f"{os.sep}.lake{os.sep}packages{os.sep}" in p]
    return ("infra", "the solution's package imports do not load (infrastructure, not a "
            f"verdict on the submission): the probe compiling {sorted(set(pkg))} exited {rc}"
            + (" (killed by signal %d)" % -rc if rc < 0 else "")
            + (f"; package build directories on the search path: {where}" if where else "")
            + (f"; its output:\n{tail(out)}" if out.strip() else "; it printed nothing "
               "(an olean truncated by a crash or a full disk makes Lean die silently)"))


# The package directory names (as in the manifest, `manifest_path()`) of PACKAGE_ROOTS.
PACKAGE_NAMES = {"Mathlib": "mathlib", "Batteries": "batteries", "Aesop": "aesop", "Qq": "Qq",
                 "ProofWidgets": "proofwidgets", "Plausible": "plausible",
                 "ImportGraph": "importGraph", "LeanSearchClient": "LeanSearchClient"}


def package_revisions():
    """name -> {"manifest": the revision the manifest (`manifest_path()`) pins, "checkout": the
    HEAD of the checkout in the packages directory (None if it cannot be read)} for the
    admitted packages. A different checkout can have a different simp set and different lemma
    names under the same Lean version, so the same Solution.lean could be accepted on one machine
    and rejected on another; `check` makes a mismatch an infrastructure error."""
    try:
        with open(manifest_path()) as fh:
            pins = {p["name"]: p.get("rev") for p in json.load(fh).get("packages", [])}
    except (OSError, ValueError, KeyError):
        pins = {}
    dirs = package_dirs()
    out = {}
    for root in PACKAGE_ROOTS:
        name = PACKAGE_NAMES[root]
        if name not in dirs:
            continue
        try:
            head = subprocess.run(["git", "-C", dirs[name], "rev-parse", "HEAD"],
                                  capture_output=True, text=True, timeout=30,
                                  env=sandbox.scrubbed_env()).stdout.strip()
        except (OSError, subprocess.SubprocessError):
            head = ""
        out[name] = {"manifest": pins.get(name), "checkout": head or None}
    return out


def revision_mismatches(revs):
    """The packages whose checkout is not the revision the manifest pins (both known)."""
    return sorted(n for n, r in revs.items()
                  if r["manifest"] and r["checkout"] and r["manifest"] != r["checkout"])


def search_path_from(out):
    """The directories of `lake env printenv LEAN_PATH` (the last line of `out`: lake may print
    warnings before it)."""
    lines = [ln for ln in out.splitlines() if ln.strip()]
    return [p for p in (lines[-1].strip().split(":") if lines else []) if p]


def packages_missing_from(search_path, pkg):
    """The package roots among the imports `pkg` that no search-path entry provides (Lean
    resolves a module root to the first entry with a directory `Root` or a file `Root.olean`)."""
    roots = sorted({m.split(".")[0] for m in pkg})
    return [r for r in roots
            if not any(os.path.isdir(os.path.join(e, r)) or os.path.isfile(os.path.join(e, r + ".olean"))
                       for e in search_path)]


def olean_files(root):
    """path -> metadata (size, mtime, ctime, inode, mode) of every `.olean*` file (the
    exported, `.server` and `.private` parts: what `import` loads and what the comparator and
    `leanchecker` read) under the directory `root`."""
    snap = {}
    for dirpath, dirnames, names in os.walk(root):
        dirnames.sort()
        for n in sorted(names):
            if ".olean" in n and not n.endswith((".hash", ".trace")):
                p = os.path.join(dirpath, n)
                st = os.lstat(p)
                snap[p] = (f"meta:{st.st_size}:{st.st_mtime_ns}:{st.st_ctime_ns}:"
                           f"{st.st_ino}:{st.st_mode}")
    return snap


def search_path_snapshot(search_path, skip=()):
    """The tripwire's view of the Lean SEARCH PATH (`lake env printenv LEAN_PATH`: what the solution
    compile, the comparator and `leanchecker` all resolve modules through), path -> digest:

      * an entry that does not exist is recorded as ABSENT, so creating it is a difference (Lean
        resolves a module root to the FIRST entry that has a directory of that name, and `lake
        env` puts `Cli`'s build directory, which this machine has never built, ahead of
        Mathlib's: a `Cli/.lake/build/lib/lean/Mathlib/` planted by a solution would shadow
        Mathlib for every later run);
      * the top-level names of every entry (a new module root, or a removed one, shadows or hides
        a package);
      * the `.olean*` metadata of every file under every entry NOT in `skip` (the package
        builds; `skip` is what other parts of the tripwire already cover in a way that
        tolerates unrelated builds: the stage, the toolchain, the svGolf and LeanModels
        builds). About 33,000 files and 0.3 s for the closure of Mathlib's eight packages.
    """
    snap = {}
    skip = tuple(os.path.realpath(s) for s in skip)
    for e in search_path:
        if not os.path.lexists(e):
            snap[f"search-path entry: {e}"] = "absent"
            continue
        if os.path.isdir(e):
            snap[f"search-path entry: {e}"] = "names:" + ",".join(
                sorted(n + ("/" if os.path.isdir(os.path.join(e, n)) else "")
                       for n in os.listdir(e)))
        rp = os.path.realpath(e)
        if any(rp == s or rp.startswith(s + os.sep) for s in skip):
            continue
        for p, m in olean_files(e).items():
            snap.setdefault(p, m)
    return snap


# The marker lines the generated `Submission.Design` prints (WP-C3, below).
UNSUPPORTED_AT = re.compile(r"SVGOLF_UNSUPPORTED at (.*)")
UNSUPPORTED_FREE = re.compile(r"SVGOLF_UNSUPPORTED_FREE (\d+)")


def unsupported_check_points(task):
    """The points whose lowered design the `design` stage tests for an Unsupported
    node: the SCORING point first (the one every later stage runs, simulates and
    scores), then the other points of the extractor's cross-check (probe and
    backstop points) that are not larger than it in any parameter. The larger ones
    are skipped for cost only: evaluating `design.sem` in Lean's interpreter at
    `mul_tree`'s N = 32 takes 25 s, the scoring point 6 s, and a design loud only
    there has no proof of its `forall N` statement anyway. A fixed-size task has the
    one design: `[None]`."""
    names = [p["name"] for p in task.get("parameters", [])]
    if not names:
        return [None]
    top = parse_point(task["scoring"]["params"])
    return [top] + [p for p in probe_points(task)
                    if p != top and all(p[n] <= top[n] for n in names)]


def unsupported_check_text(task):
    """The generated `#eval` that rejects a design with an Unsupported node
    (WP-C3). `load_design_sv2` accepts an envelope whose lowered design has a
    loud `Unsupported` process, statement or expression (a procedural
    function call, a construct ls-sv does not run): `design.sem` is then a
    design that ls-sv cannot execute, no proof about it can hold, and
    without this the failure surfaced only as an opaque proof error or at the
    `postsynth` stage. Here `Design2.hasUnsupported` is tested at the points of
    `unsupported_check_points`, and the first node found (`Design2.firstLoud`:
    kind and text) is named in the error, before any proof, scoring or
    leaderboard work. On success it prints `SVGOLF_UNSUPPORTED_FREE <points>`,
    which `check` requires (a check that did not run is an infrastructure
    error, not a pass)."""
    names = [p["name"] for p in task.get("parameters", [])]
    entries = [("default", "") if p is None else
               (point_str(p), " ".join(str(p[n]) for n in names))
               for p in unsupported_check_points(task)]
    items = ",\n    ".join(f"({lean_string(label)}, design.sem{' ' + args if args else ''})"
                           for label, args in entries)
    return f"""/-! Every point's lowered design must be free of `Unsupported` nodes (WP-C3). -/
#eval show IO Unit from do
  let pts : List (String × LeanModels.Sv.Design2) := [
    {items}]
  for (p, d) in pts do
    if d.hasUnsupported then
      let what := match d.firstLoud with
        | some (k, t) => s!"{{k}}: {{t}}"
        | none => "(an unsupported node)"
      throw <| IO.userError s!"SVGOLF_UNSUPPORTED at {{p}}: {{what}}"
  IO.println s!"SVGOLF_UNSUPPORTED_FREE {{pts.length}}"
"""


# The task kinds (task.json `kind`). The CLOCKED kinds (PLAN4 Gate 2; svgolf/design/sequential/
# CONTRACT.md, txtask-v1) name their clock port in task.json `clock`, which the source gate's clocked
# rules check (score/srcgate.py, item 6): `seq-family`, a `SeqTask` statement `Statement design.sem`
# (the counter fixture); `tx-family`, a `TxTask` statement `Statement design.sem lat` with the
# latency function the SOLUTION defines (`LATENCY_DEF`) and declares at the scoring point in its
# header (`-- svgolf-latency: n`, C3): the goal is `Statement design.sem lat ∧ lat p₀ = n`;
# `stream-family`, a `StreamTask` statement (C8: the sorter) of the same shape, whose task.json
# `protocol` names the stream ports and the parameter that is the number of values (`count`);
# `react-family`, a `ReactTask` statement (SvGolf/TaskReact.lean: the arbiter) `Statement design.sem`, a
# controller that runs for ever under a safety monitor and bounded response, with no latency (one
# decision per cycle: the score's time is the clock period), whose task.json names its `reset` port (the
# reactive post-synthesis check drives segments of reset-free entries, check/postsynth.py "THE
# REACTIVE CHECK"). Being clocked, its source gets the clocked rules: the loader drops an asynchronous
# reset, a `negedge` clock and an `iff` guard, which the gate refuses (design/reactive/README.md H2).
KINDS = ("comb-family", "comb-fixed", "seq-family", "tx-family", "stream-family", "react-family")
CLOCKED_KINDS = ("seq-family", "tx-family", "stream-family", "react-family")
LATENCY_KINDS = ("tx-family", "stream-family")
STREAM_PORTS = ("start", "in_valid", "in_data", "out_valid", "out_data")
LATENCY_HEADER = re.compile(r"^--[ \t]*svgolf-latency:(.*)$", re.M)
LATENCY_DEF = "Submission.lat"


def task_kind(task):
    """The task's kind, checked against the task.json fields it needs (infrastructure: the task
    files are the organizer's)."""
    kind = task.get("kind")
    if kind not in KINDS:
        raise RuntimeError(f"task.json: kind {kind!r} is not one of {KINDS}")
    if kind in CLOCKED_KINDS and not (isinstance(task.get("clock"), str) and task["clock"]):
        raise RuntimeError(f"task.json: a {kind} task names its clock port (`clock`)")
    if kind in LATENCY_KINDS and not task.get("parameters"):
        raise RuntimeError(f"task.json: a {kind} task has parameters (the latency is a function of them)")
    proto = task.get("protocol") or {}
    if kind == "stream-family" and not (all(isinstance(proto.get(k), str) for k in STREAM_PORTS)
                                        and proto.get("count") in [p["name"] for p in task["parameters"]]):
        raise RuntimeError(f"task.json: a stream-family task's `protocol` names the ports {STREAM_PORTS} and "
                           "the parameter that is the number of values (`count`)")
    if kind == "react-family" and not (isinstance(task.get("reset"), dict) and isinstance(task["reset"].get("port"), str)
                                       and task["reset"].get("level", 1) in (0, 1)):
        raise RuntimeError("task.json: a react-family task names its synchronous reset (`reset`: `port`, `level`)")
    return kind


def parse_latency(text, kind):
    """The latency `n` the solution's header declares (`-- svgolf-latency: n`, a line of its
    own): exactly one such line, n ≥ 1 (C3), for a `LATENCY_KINDS` task; none for any other kind."""
    found = LATENCY_HEADER.findall(text)
    if kind not in LATENCY_KINDS:
        if found:
            raise Reject("latency", f"a `-- svgolf-latency:` line is for tx-family and stream-family tasks; this task "
                         f"is {kind} and its statement has no latency")
        return None
    if len(found) != 1:
        raise Reject("latency", "the solution declares its latency in exactly one header line "
                     f"`-- svgolf-latency: <n>` (found {len(found)}); the goal pins "
                     f"`{LATENCY_DEF} p₀ = n` at the scoring point and the score uses n (C3)")
    m = re.fullmatch(r"\s*([1-9][0-9]{0,8})\s*", found[0])
    if not m:
        raise Reject("latency", f"`-- svgolf-latency:{found[0]}`: the latency is a decimal "
                     "number of cycles, 1 to 999999999 (C3: lat ≥ 1)")
    return int(m.group(1))


def goal_text(task, latency=None):
    """The generated `Goal`: `abbrev Goal : Prop := <Statement> design.sem`, or for a `LATENCY_KINDS`
    task the function of the solution's latency `lat` (one `Nat` per parameter, curried like
    `design.sem`) that pins it at the scoring point to the header's `latency`; the comparator
    checks `Goal Submission.lat` (`--goal-arg`, check/Comparator.lean point 7)."""
    const = task["statement"]["constant"]
    if task_kind(task) not in LATENCY_KINDS:
        return f"abbrev Goal : Prop := {const} design.sem"
    names = [p["name"] for p in task["parameters"]]
    p0 = parse_point(task["scoring"]["params"])
    ty = " → ".join(["Nat"] * (len(names) + 1))
    args = " ".join(str(p0[n]) for n in names)
    return (f"abbrev Goal (lat : {ty}) : Prop :=\n"
            f"  {const} design.sem lat ∧ lat {args} = {int(latency)}")


# F8 (decided 2026-11-08): THE LATENCY AT EVERY POST-SYNTHESIS POINT. The statement holds `lat p` at every point p in
# range, and the score uses the header's n = `lat p₀` at the scoring point only; the clocked post-synthesis check of a
# latency kind runs at several points (`clocked_points`), each against THAT point's latency `lat p` (before, the scoring
# point's n at every point: an over-rejection of a design whose latency is larger elsewhere, e.g. one that grows with N
# when the scoring point is not the largest). A proved run asks the comparator for `lat p` at each point (point 8 of
# check/Comparator.lean: the kernel reduces `Submission.lat a b …` to a literal and accepts `… = v` by `Eq.refl v`; no
# compiled code of the submission runs); an `--unproved` run has no `lat` and takes `--latency-at POINT:n`, else the
# scoring point's `--latency n`. The result records the values (`latency_at`, by point) and each point's record its own.
LATENCY_MAX = 999999999      # the header's largest n (`parse_latency`); a larger `lat p` is refused at `latency`


def clocked_points(task):
    """The clocked post-synthesis check's points: the task's `postsynth.points`, the scoring point first when they do
    not list it (the scored netlist is always checked)."""
    sparams = score.task_scoring_point(task)[1]
    points = [{n: int(v) for n, v in pt.items()} for pt in postsynth.config(task)["points"] or []]
    return ([] if sparams in points else [sparams]) + points


def parse_latency_at(items):
    """`--latency-at POINT:n` (repeatable; POINT as `N=3,W=4`) as {point text: n}; ValueError on a malformed item."""
    out = {}
    for it in items or ():
        pt, sep, n = it.rpartition(":")
        m = re.fullmatch(r"\s*([1-9][0-9]{0,8})\s*", n)
        if not sep or not m:
            raise ValueError(f"--latency-at {it!r}: give POINT:n, e.g. N=3,W=4:6 (n a latency, 1 to {LATENCY_MAX})")
        key = point_str(parse_point(pt))
        if key in out and out[key] != int(m.group(1)):
            raise ValueError(f"--latency-at names the point {key} twice, with {out[key]} and {m.group(1)}")
        out[key] = int(m.group(1))
    return out


def unproved_latency_at(task, latency, given):
    """An `--unproved` run's latency at every clocked point: `given` (`--latency-at`) where it names the point, else the
    scoring point's `latency`. RuntimeError (a usage error) for a point that is not checked, or a scoring point given
    another value than `--latency`."""
    pts = [point_str(p) for p in clocked_points(task)]
    s0 = point_str(score.task_scoring_point(task)[1])
    stray = sorted(set(given) - set(pts))
    if stray:
        raise RuntimeError(f"--latency-at names {stray}, not among the clocked post-synthesis points {pts}")
    if given.get(s0, latency) != latency:
        raise RuntimeError(f"--latency-at {s0}:{given[s0]} is the scoring point, whose latency is --latency {latency}")
    return {p: given.get(p, latency) for p in pts}


def latency_at_from_comparator(task, comp, latency):
    """A proved run's latency at every clocked point, from the comparator's `goal_arg_at` (point 8): {point text: n}.
    Reject("latency") for a point the kernel gave no number, or one beyond LATENCY_MAX; RuntimeError (infrastructure)
    for a report that does not answer every point asked, or a scoring point other than the declared n (the kernel
    accepted the goal, which pins `lat p₀ = n`)."""
    names = [p["name"] for p in task["parameters"]]
    pts = clocked_points(task)
    got = comp.get("goal_arg_at")
    if not isinstance(got, list) or [e.get("args") if isinstance(e, dict) else None for e in got] != \
            [[p[n] for n in names] for p in pts]:
        raise RuntimeError(f"the comparator did not report the latency at the points asked ({[point_str(p) for p in pts]}): "
                           f"{json.dumps(got)[:400]}")
    out = {}
    for p, e in zip(pts, got):
        v = e.get("value")
        if not isinstance(v, int) or isinstance(v, bool):
            raise Reject("latency", f"the kernel gives no number for `{LATENCY_DEF}` at {point_str(p)}, a point of the "
                         f"clocked post-synthesis check, which runs each point against its own latency: "
                         f"{e.get('error') or e}")
        if not 1 <= v <= LATENCY_MAX:
            raise Reject("latency", f"`{LATENCY_DEF}` is {v} at {point_str(p)}, a point of the clocked post-synthesis "
                         f"check: the checker simulates latencies 1 to {LATENCY_MAX}")
        out[point_str(p)] = v
    s0 = point_str(score.task_scoring_point(task)[1])
    if out.get(s0, latency) != latency:
        raise RuntimeError(f"the kernel gives {LATENCY_DEF} at the scoring point {s0} = {out[s0]}, but the goal it "
                           f"accepted pins it to the declared {latency} (infrastructure: report this)")
    return out


def comparator_report(out, goal_arg=None):
    """The comparator's `SVGOLF_COMPARATOR {…}` report in its output `out`, or None. The report's
    `goal_arg` key is the tx-family's (`--goal-arg`, check/Comparator.lean point 7); a run given no
    goal argument reports it `null`, and the key is dropped there, so the result of a kind without
    one stays character for character what it was before tx-family (the byte-identity goldens,
    tests/checker/ppa_wiring/). A non-null `goal_arg` is always kept."""
    m = re.search(r"SVGOLF_COMPARATOR (\{.*\})", out)
    if m is None:
        return None
    comp = json.loads(m.group(1))
    if goal_arg is None and isinstance(comp, dict) and "goal_arg" in comp and comp["goal_arg"] is None:
        del comp["goal_arg"]
    return comp


def design_module_text(task, envelope_path, latency=None):
    stmt = task["statement"]
    return f"""import LeanModels.Sv.Ingest2
import {stmt["module"]}

/-!
GENERATED by svgolf/check.py for task `{task["name"]}`. Do not edit: this file
is trusted. It loads the envelope that the pinned extractor produced from the
submitted SystemVerilog, and names the exact statement the submission proves.
-/

namespace Submission

load_design_sv2 design from {lean_string(envelope_path)}

/-- The statement this submission must prove: task `{task["name"]}`. -/
{goal_text(task, latency)}

{unsupported_check_text(task)}
end Submission
"""


# THE PORTS (decided 2026-11-07, the arbiter's mutation sweep, finding F-a): the `extract` stage refuses a top module
# whose ports at a probe point (every point of the extractor's sidecar; a task without probe points: the module at its
# defaults) differ from task.json `ports`: the input ports in declaration order, each with its width, are exactly
# `ports.inputs` (the clock and the reset of a clocked kind among them), the output ports likewise `ports.outputs`, and
# no port has another direction. It is the statement's `Interface` (SvGolf/Task.lean `inputPorts d = t.inputs N ∧
# outputPorts d = t.outputs N`; TaskSeq.lean / TaskReact.lean the same) at those points, checked before any proof:
# without it a port one bit wider (`input logic [N-0:0] req`) passed every check that needs no proof, and only the
# proof, which cannot exist, stood in its way. A width in task.json is an expression of the task's parameters.
_WIDTH_OPS = {ast.Add: lambda a, b: a + b, ast.Sub: lambda a, b: a - b, ast.Mult: lambda a, b: a * b,
              ast.FloorDiv: lambda a, b: a // b}


def port_width(expr, params):
    """task.json's port width `expr` (a string: integers, the parameters' names, + - * // and parentheses) at
    `params` ({name: int}). Anything else is an infrastructure error (the task's file is wrong), never a verdict."""
    def ev(n):
        if isinstance(n, ast.Expression):
            return ev(n.body)
        if isinstance(n, ast.Constant) and isinstance(n.value, int) and not isinstance(n.value, bool):
            return n.value
        if isinstance(n, ast.Name) and n.id in params:
            return int(params[n.id])
        if isinstance(n, ast.BinOp) and type(n.op) in _WIDTH_OPS:
            return _WIDTH_OPS[type(n.op)](ev(n.left), ev(n.right))
        raise RuntimeError(f"task.json `ports`: the width {expr!r} is not an expression of the parameters "
                           f"{sorted(params)} (integers, + - * // and parentheses)")
    try:
        return ev(ast.parse(str(expr), mode="eval"))
    except SyntaxError:
        raise RuntimeError(f"task.json `ports`: the width {expr!r} does not parse")


def width_words(w):
    """A width in words: `1 bit`, `N bits`."""
    return "1 bit" if w == 1 else f"{w} bits"


def port_problems(task, top, envl, sidecar):
    """([why], [checked point names]): how the top module's ports differ from task.json `ports` at each probe point
    (the extractor's sidecar `sidecar`, its every point) or, without probe points, at the defaults (the envelope
    `envl`'s module); [] when they agree everywhere. A port's width is the extractor's `resolved` width. A view with
    a port the extractor could not read (an `Unsupported` node) is not judged here: the `design` stage refuses the
    envelope with the construct's name."""
    want = task.get("ports") or {}
    if sorted(want) != ["inputs", "outputs"]:
        raise RuntimeError("task.json `ports` must have exactly `inputs` and `outputs`")
    views = []
    if sidecar:
        with open(sidecar) as fh:
            side = json.load(fh)
        for p in side.get("points") or []:
            mod = p.get("module") or {}
            over = {o["name"]: o["value"] for o in p.get("overrides") or []}
            params = {q.get("name"): q.get("resolved") for q in mod.get("params", [])
                      if q.get("kind") == "ParameterDecl" and isinstance(q.get("resolved"), int)}
            params.update(over)          # the point's own values; a parameter it leaves alone: the resolved default
            views.append((point_str(over) or "default", params, mod))
        if not views:
            raise RuntimeError("the extractor's probe sidecar has no points")
    else:
        mods = [m for m in envl["design"]["modules"] if m.get("name") == top]
        mod = mods[0] if mods else {}
        params = {q.get("name"): q.get("resolved") for q in mod.get("params", []) if q.get("kind") == "ParameterDecl"}
        views.append(("the defaults", params, mod))
    bad, judged = [], []
    for name, params, mod in views:
        if mod.get("name") != top:
            raise RuntimeError(f"the extractor's view at {name} is not the module `{top}`")
        if any(q.get("kind") != "Port" for q in mod.get("ports") or []):
            continue       # a port the extractor could not read (`Unsupported`): the `design` stage refuses it, by name
        judged.append(name)
        got = {"in": [], "out": []}
        for q in mod.get("ports") or []:
            w = (q.get("width") or {}).get("resolved")
            if q.get("dir") not in got:
                bad.append(f"at {name}: port `{q.get('name')}` is `{q.get('dir')}`; a task's ports are inputs and "
                           "outputs")
                continue
            got[q["dir"]].append((q.get("name"), w))
        for d, key in (("in", "inputs"), ("out", "outputs")):
            exp = [(e["name"], port_width(e["width"], params)) for e in want[key]]
            if [n for n, _ in got[d]] != [n for n, _ in exp]:
                bad.append(f"at {name}: the {key} are {[n for n, _ in got[d]]} (in declaration order), the task's "
                           f"are {[n for n, _ in exp]}")
                continue
            bad += [f"at {name}: {key[:-1]} `{n}` is {width_words(gw)} wide, the task's is {width_words(ew)}"
                    for (n, gw), (_, ew) in zip(got[d], exp) if gw != ew]
    return bad, judged


# The solution's own build output, the only files the solution compile may
# create or change in the staging tree.
def _is_solution_output(stage, path):
    rel = os.path.relpath(path, stage)
    return (os.path.dirname(rel) == os.path.join("build", "Submission")
            and os.path.basename(rel).startswith("Solution."))


def _tool_trees():
    """Directories and files the later stages EXECUTE or LOAD: the Lean
    toolchain (lean, lake, leanchecker, the core oleans), Yosys (its binary,
    yosys-abc, its techmap library), and elan's settings (a toolchain
    override would swap the toolchain). The simulator (Verilator, the C++
    compiler, make) is `postsynth.tool_paths()`."""
    out = []
    try:
        lean = subprocess.run(["elan", "which", "lean"], cwd=SVGOLF, capture_output=True,
                              text=True, timeout=60, env=sandbox.scrubbed_env()).stdout.strip()
        if lean:
            tc = os.path.dirname(os.path.dirname(os.path.realpath(lean)))
            out += [os.path.join(tc, "bin"), os.path.join(tc, "lib")]
    except Exception:
        pass
    out.append(os.path.join(os.path.expanduser("~"), ".elan", "settings.toml"))
    ys = shutil.which(os.environ.get("SVGOLF_YOSYS") or "yosys")
    if ys:
        ys = os.path.realpath(ys)
        out += [ys, os.path.join(os.path.dirname(ys), "yosys-abc"),
                os.path.join(os.path.dirname(os.path.dirname(ys)), "share", "yosys")]
    return out + postsynth.tool_paths()


# The trusted files only a CLOCKED check reads (relative to svgolf/), fingerprinted by content like the
# combinational flow's (`integrity_snapshot`; leaderboard.py CHECKER_FILES names the same files)
CLOCKED_TRUSTED = (("score", "svgolf_seq.ys"), ("score", "ge_seq.json"), ("check", "clocked_rules.py"))


def integrity_snapshot(stage, search_path=()):
    """path -> digest. By CONTENT (sha256): every file of the staging tree
    (except the solution's own output) and the trusted scripts. By METADATA
    (size, mtime, ctime, inode, mode; ctime cannot be set by a user process):
    the svGolf and LeanModels.Sv/Core builds, the Lean toolchain and Yosys, and, for EVERY
    solution (WP-B review: a solution that imports no package can still plant an olean that a
    later Mathlib-importing run would load), the Lean search path `search_path`
    (`search_path_snapshot`): the `.olean*` files of the package builds on it, its entries'
    top-level names, and the entries that do not exist (recorded as absent). New and deleted
    files are differences too."""
    snap = {}

    def walk(root):
        if os.path.isfile(root) or os.path.islink(root):
            yield root
            return
        for dirpath, dirnames, names in os.walk(root):
            dirnames.sort()
            for n in sorted(names):
                yield os.path.join(dirpath, n)

    def meta(p):
        st = os.lstat(p)
        return f"meta:{st.st_size}:{st.st_mtime_ns}:{st.st_ctime_ns}:{st.st_ino}:{st.st_mode}"

    for p in walk(stage):
        if not _is_solution_output(stage, p):
            snap[p] = "sha256:" + sha256_file(p) if os.path.isfile(p) else meta(p)
    content = [os.path.abspath(__file__), COMPARATOR, *envelope.extractor_files(), ENVELOPE_PY, SVEVAL_SRC,
               os.path.join(SVGOLF, "lakefile.toml"), os.path.join(SVGOLF, "lean-toolchain"),
               os.path.join(SVGOLF, "lake-manifest.json"),
               os.path.join(LS_ROOT, "lakefile.toml"), os.path.join(LS_ROOT, "lean-toolchain"),
               os.path.join(LS_ROOT, "lake-manifest.json")]   # pins Mathlib's revision (WP-B)
    content += [os.path.join(SVGOLF, "score", f) for f in
                 ("score.py", "banlist.py", "srcgate.py", "fourstate.py", "slangdriver.py", "canon.ys",
                 "svgolf.ys", "ge.json", "ppa.py", "ppa_pins.json", "ppa_mapped.ys",
                 "ppa_mapped_pins.json")]
    # the clocked kinds' own trusted files (2026-11-07): the clocked flow and its GE table, which score a clocked
    # design (score.py `FLOWS["seq"]`), and the clocked source rules (`clocked_rules` stage)
    content += [os.path.join(SVGOLF, *f) for f in CLOCKED_TRUSTED]
    try:
        content += postsynth.trusted_files()   # the evaluator binary, postsynth.py, simcells.v
    except postsynth.InfraError:
        pass   # reported by the postsynth stage itself
    content += sandbox.trusted_files()         # check/sandbox/**: the sandbox is part of the trusted base
    for p in content:
        if os.path.isfile(p):
            snap[p] = "sha256:" + sha256_file(p)
    lib = os.path.join(LS_ROOT, ".lake", "build", "lib", "lean", "LeanModels")
    trees = [os.path.join(SVGOLF, ".lake", "build"), os.path.join(lib, "Sv"),
             os.path.join(lib, "Core")] + [os.path.join(lib, f) for f in os.listdir(lib)
                                           if f.startswith(("Sv.", "Core."))] \
        if os.path.isdir(lib) else [os.path.join(SVGOLF, ".lake", "build")]
    tools = _tool_trees()
    for root in trees + tools:
        if os.path.lexists(root):
            for p in walk(root):
                snap.setdefault(p, meta(p))
    # what the lines above already cover is skipped by the search-path walk
    covered = [os.path.join(stage, "build"), os.path.join(SVGOLF, ".lake", "build"),
               os.path.join(LS_ROOT, ".lake", "build")] + tools
    for p, m in search_path_snapshot(search_path, skip=covered).items():
        snap.setdefault(p, m)
    return snap


def integrity_diff(before, after):
    return sorted(f for f in set(before) | set(after) if before.get(f) != after.get(f))


def git_rev(path):
    try:
        rev = subprocess.run(["git", "-C", path, "rev-parse", "HEAD"], capture_output=True,
                             text=True, check=True, env=sandbox.scrubbed_env()).stdout.strip()
        dirty = subprocess.run(["git", "-C", path, "status", "--porcelain", "--", "LeanModels/Sv",
                                "extractors/sv"], capture_output=True, text=True,
                               env=sandbox.scrubbed_env()).stdout.strip()
        return rev + ("+dirty" if dirty else "")
    except Exception:
        return None


# ---------------------------------------------------------------------------
# the checker
# ---------------------------------------------------------------------------

def incomplete_reasons(task, st, do_score, build_trusted, time_limit):
    """Why an ACCEPTED result is INCOMPLETE (each reason a sentence), or [] for a complete one: the check left part of
    itself out, so it establishes nothing a board may rank (README.md, "Rules"). `--no-score` (no score, no
    post-synthesis check, no sky130 columns); a LIGHT post-synthesis check (a subset of the vectors, at any point);
    `--no-trusted-build` (the comparator checked the goal against whatever statement module was on disk); a
    `--time-limit` other than the task's (the proof ran under another limit)."""
    why = []
    if not do_score:
        why.append("--no-score: no score, no post-synthesis check and no sky130 columns were made")
    else:
        ps = st.get("postsynth") or {}
        modes = ({ps.get("mode")} if "mode" in ps else
                 {p.get("mode") for p in ps.get("points") or [] if isinstance(p, dict)})
        if "light" in modes:
            why.append("the post-synthesis check ran LIGHT (a subset of the vectors, for local feedback): "
                       "rerun with --postsynth full")
    if not build_trusted:
        why.append("--no-trusted-build: this run did not build the trusted modules, so the comparator checked the "
                   "goal against whatever statement module was on disk")
    task_limit = task.get("time_limit_s", 600)
    if time_limit is not None and time_limit != task_limit:
        why.append(f"--time-limit {time_limit:g}: the proof ran under another limit than the task's {task_limit:g} "
                   "CPU s")
    return why


def fourstate_points(task):
    """The points of the `fourstate` stage: the scoring point first (the design that is scored), then the task's probe
    and backstop points (`probe_points`), each once. A parameterless top has the one point {}."""
    first = score.task_scoring_point(task)[1]
    return [first] + [p for p in probe_points(task) if p != first]


def check(task_dir, sv_path, lean_path, stage, wrap, time_limit=None, do_score=True,
          build_trusted=True, unproved=False, keep=False, tactics=False, postsynth_mode=None,
          ppa_mode="auto", latency=None, latency_at=None):
    """Check one submission. With `unproved` (and `lean_path` None), run every
    stage that needs no proof and stop at the pseudo-stage `unproved`, never
    accepting; with `tactics` (only then), also run the advisory fragment
    pre-check after the `design` stage. With `keep`, the postsynth work
    directory (netlist, vectors, simulator outputs) is kept and named in the
    result. `postsynth_mode` is "light" or "full" (None: `$SVGOLF_POSTSYNTH`,
    else light; check/postsynth.py, "TWO MODES"); the result's
    `stages.postsynth.mode` says which ran. `ppa_mode` is "auto", "off" or
    "require" (the `ppa` stage, below): "require" opens the pinned liberty NOW,
    before any work, and an absent or wrong file is an infrastructure error.
    `latency_at` ({point text: n}, `--latency-at`) is an `--unproved` run's latency at the clocked
    post-synthesis points other than the scoring point (F8; a proved run asks the kernel)."""
    try:
        postsynth_mode = postsynth.resolve_mode(postsynth_mode)
    except postsynth.InfraError as e:
        raise RuntimeError(str(e))
    if ppa_mode not in PPA_MODES:
        raise RuntimeError(f"ppa mode {ppa_mode!r} is not one of {PPA_MODES}")
    res = {"task": None, "accepted": False, "stage": None, "errors": [], "stages": {},
           "stage_dir": stage}
    st = res["stages"]
    pol = sandbox.policy()
    pol.reset_note()
    if pol.mode != "off":      # `--sandbox off` (and a library caller that never configured one) adds no key
        res["sandbox"] = pol.report()
    # The postsynth stage's files live OUTSIDE the staging tree, whose every
    # file the integrity tripwire fingerprints before the solution build, in
    # a directory created only when the score stage starts (after the
    # solution's build has run).
    ps_work = {}
    if ppa_mode == "require" and do_score:
        # an official run must not spend minutes of Lean and simulation before it learns that the
        # pinned liberty is missing: open it (sha256 verified) before anything else
        try:
            ps_work["ppa_lib"] = ppa.open_library()
            ps_work["ppa_mpins"] = ppa.MappedPins(ps_work["ppa_lib"][1])     # flow A1''s pins and script, readable too
        except (ppa.PpaError, OSError) as e:
            raise RuntimeError(f"ppa: {ppa_reason(e)}")
    try:
        # task
        with open(os.path.join(task_dir, "task.json")) as fh:
            task = json.load(fh)
        res["task"] = task["name"]
        # The advisory functional oracle (check/postsynth.py), loaded NOW, before
        # any submission code runs.
        oracle = postsynth.load_oracle(task_dir, task)
        top = task["top"]
        pnames = [p["name"] for p in task.get("parameters", [])]
        limit = time_limit or task.get("time_limit_s", 600)
        vlimit = task.get("verify_time_limit_s", VERIFY_TIME_LIMIT_S)
        kind = task_kind(task)
        st["task"] = {"top": top, "parameters": pnames, "time_limit_s": limit,
                      "verify_time_limit_s": vlimit,
                      "statement": task["statement"]["constant"]}
        if kind in CLOCKED_KINDS:      # (a combinational result stays byte-identical)
            st["task"]["kind"] = kind
        if kind in CLOCKED_KINDS and do_score:
            # the ranked clocked score is sky130 (C7): the pinned liberty is required, and the
            # evaluator of the clocked post-synthesis check is binding (check/postsynth.py)
            ppa_mode = "require"
            oracle = postsynth.clocked_oracle(oracle, kind)
        if (latency is not None) != (unproved and kind in LATENCY_KINDS):
            raise RuntimeError("--latency is given exactly for an --unproved run of a tx-family or stream-family task "
                               "(a proved run reads it from the solution's header)")
        if latency_at and latency is None:
            raise RuntimeError("--latency-at is for an --unproved run of a tx-family or stream-family task, with "
                               "--latency (a proved run asks the kernel for the solution's `lat` at every point)")
        # `bv_decide` is not supported (BV_DECIDE_SUPPORTED, above): absent or false forbids it, true is an
        # infrastructure error, not a verdict. With the constant True (the tests of the dormant groundwork)
        # the default is allowed and the comparator re-verifies the axiom (check/Comparator.lean, point 6).
        allow_bv = task.get("allow_bv_decide", BV_DECIDE_SUPPORTED)
        if not isinstance(allow_bv, bool):
            raise RuntimeError(f"task.json: allow_bv_decide must be false or absent, not {allow_bv!r}")
        if allow_bv and not BV_DECIDE_SUPPORTED:
            raise RuntimeError("task.json sets allow_bv_decide: true, but the checker does not support external SAT "
                               "solvers (decided 2026-11-01): allow_bv_decide must be false or absent "
                               "(README.md, \"bv_decide\")")
        # sky130_a0_v3: the task's `input_drive` (absent: the pins' default) is one of the pins' allowed cells. A defect
        # of the task's configuration, never of the design: reported NOW, before any Lean stage, by every run that will
        # weigh (the ppa stage would raise the same error after the whole check); it needs the pins file, not the liberty
        if do_score and ppa_mode != "off":
            try:
                pins = ps_work["ppa_lib"][1] if "ppa_lib" in ps_work else ppa.Pins()
            except ppa.PpaError:
                pins = None       # an unreadable pins file: the ppa stage reports it as it always did (auto: a reason)
            if pins is not None:
                try:
                    ppa.input_drive_of(task, pins)
                except ppa.TaskConfigError as e:
                    raise RuntimeError(f"ppa: {ppa_reason(e)}")

        # imports
        imports = []
        if not unproved:
            with open(lean_path) as fh:
                lean_text = fh.read()
            imports = parse_header(lean_text)
            bad = [m for m in imports if not any(re.fullmatch(p, m) for p in IMPORT_ALLOW)]
            st["imports"] = {"imports": imports, "rejected": bad}
            if bad:
                raise Reject("imports", f"imports outside the allowlist: {bad}")
            if "Submission.Design" not in imports:
                raise Reject("imports", "the solution must `import Submission.Design` (the "
                             "generated design module that defines `Submission.design` and "
                             "`Submission.Goal`)")
            latency = parse_latency(lean_text, kind)
        if latency is not None:
            res["latency"] = latency
            st["latency"] = {"declared": latency, "definition": LATENCY_DEF,
                             "at": task["scoring"]["params"]}
            if unproved and do_score:
                # F8: no `lat` to evaluate; the command line's values, else the scoring point's n
                res["latency_at"] = unproved_latency_at(task, latency, latency_at or {})
                st["latency"]["points"] = res["latency_at"]
                st["latency"]["points_from"] = ("--latency-at, else the scoring point's --latency" if latency_at else
                                                "the scoring point's --latency (no --latency-at)")

        # source gate: the stage gets the CANONICAL text, and every later
        # stage (extractor, banlist, Yosys) reads it, never the submitted file
        os.makedirs(os.path.join(stage, "Submission"), exist_ok=True)
        sv = os.path.join(stage, "design.sv")
        shown = os.path.basename(sv_path)
        try:
            canon, findings = envelope.gate(sv_path, name=shown,
                                            clock=task["clock"] if kind in CLOCKED_KINDS else None)
        except envelope.InfraError as e:
            raise RuntimeError(str(e))
        st["source"] = {"sha256": sha256_file(sv_path), "findings": findings}
        if findings:
            raise Reject("source", "the design text is refused (the extractor and Yosys would "
                         "read different programs, or give it different meanings):\n"
                         + "\n".join(findings[:8]))
        with open(sv, "w", newline="") as fh:
            fh.write(canon)
        st["source"]["canonical_sha256"] = sha256_file(sv)
        sol = os.path.join(stage, "Submission", "Solution.lean")
        if not unproved:
            shutil.copyfile(lean_path, sol)

        # extract (pinned extractor; never a player .json)
        env_path = os.path.join(stage, "design.sv.json")
        probe_pts = probe_points(task)
        stage_start("extract", "the pinned extractor" + (", probe points " + " ".join(point_str(p) for p in probe_pts)
                                                         if probe_pts else ""))
        try:
            proc, _ = envelope.run_extractor(sv, top, probe_pts, env_path)
        except envelope.InfraError as e:
            raise RuntimeError(str(e))
        # the extractor relative to lean-surfaces' root (`lean_surfaces` is that root's revision):
        # the same in both layouts, and no directory of the machine in a result
        st["extract"] = {"extractor": os.path.relpath(EXTRACTOR, LS_ROOT),
                         "extractor_sha256": envelope.extractor_sha256(),
                         "lean_surfaces": git_rev(LS_ROOT), "exit": proc.returncode,
                         # the multi-point cross-check: the sidecar that
                         # `load_design_sv2` checks in the `design` stage
                         "probe_points": [point_str(p) for p in probe_pts]}
        if proc.returncode != 0 or not os.path.exists(env_path):
            raise Reject("extract", f"the extractor refused the design:\n{tail(proc.stderr + proc.stdout)}")
        if probe_pts and not os.path.exists(envelope.sidecar_path(env_path)):
            raise RuntimeError("the extractor wrote no probe sidecar")
        with open(env_path) as fh:
            envl = json.load(fh)
        mods = [m for m in envl["design"]["modules"] if m.get("name") == top]
        # Overridable parameters only: localparams (body or header) are the
        # design's own business.
        got_params = ([p.get("name") for p in mods[0].get("params", [])
                       if p.get("kind") == "ParameterDecl"] if mods else None)
        st["extract"]["parameters"] = got_params
        if got_params != pnames:
            raise Reject("extract", f"top module `{top}` must have exactly the parameters "
                         f"{pnames} (the scoring script overrides them by name); it has {got_params}")
        # the ports at every probe point (or, with none, at the defaults) against task.json `ports` (2026-11-07)
        ports_bad = port_problems(task, top, envl, envelope.sidecar_path(env_path) if probe_pts else None)
        st["extract"]["ports_checked"] = ports_bad[1]
        if ports_bad[0]:
            raise Reject("extract", f"top module `{top}`: its ports are not the task's (task.json `ports`, the "
                         "statement's `Interface`: the input ports in declaration order with their widths, then the "
                         "output ports likewise, and no other port):\n" + "\n".join(ports_bad[0][:8]))

        # banlist (on the canonical text, which the gate already checked); it, fourstate, score and postsynth run Yosys
        if not shutil.which(os.environ.get("SVGOLF_YOSYS") or "yosys"):
            raise RuntimeError("Yosys is not on PATH (infrastructure; or SVGOLF_YOSYS names no program): the banlist, "
                               "fourstate, score and postsynth stages run it; install Yosys 0.53, with its yosys-abc")
        # `ops` is never empty: `task_banlist` adds ALWAYS_BANNED (run-time / % **) to every task's list (2026-11-06), so
        # every task runs the front check, which also reads slang's analysis errors, and the backstop. (An `else` that
        # skipped both for a task with no banned operator was removed: no task could reach it any more.)
        ops, points = banlist.task_banlist(task)
        front, diags = banlist.front_check([sv], top, ops, probe_pts + points)
        back = banlist.backstop_check([sv], top, ops, points)
        front, back, diags = ([f.replace(sv, shown) for f in xs] for xs in (front, back, diags))
        st["banlist"] = {"operators": ops, "front": front, "backstop": back,
                         "diagnostics": diags}
        if front or back or diags:
            raise Reject("banlist", "banned run-time operators (or the design does not "
                         f"elaborate): {(front + back + diags)[:6]}")

        # fourstate: at every point the checker probes, the scoring point (the design that is scored) first
        fs_points = fourstate_points(task)
        stage_start("fourstate", "the 4-state rules at " + " ".join(fourstate.point_text(p) for p in fs_points))
        try:
            fs = fourstate.check_points([sv], top, fs_points)
        except fourstate.InfraError as e:
            raise RuntimeError(f"fourstate: {e}")
        fs["findings"] = [f.replace(os.path.realpath(sv), shown).replace(sv, shown)
                          for f in fs["findings"]]
        fs["diagnostics"] = [f.replace(os.path.realpath(sv), shown).replace(sv, shown)
                             for f in fs["diagnostics"]]
        st["fourstate"] = fs
        if not fs["passed"]:
            lines = "\n".join((fs["findings"] + fs["diagnostics"])[:8])
            at = ("the scoring point" if fs["failed_point"] == fs["point"] else
                  f"{fourstate.point_text(fs['failed_point'])}, a point the statement covers (the scoring point "
                  f"{fourstate.point_text(fs['point'])} passed; the checker decides the 4-state rules at the scoring, "
                  "probe and backstop points)")
            if fs["diagnostics"]:
                # slang's own errors: a program slang reports illegal is rejected, and any finding listed with
                # them comes from slang's error recovery (WP-RB1: a slang error is not an x/z finding)
                raise Reject("fourstate", f"slang reports the program illegal at {at} "
                             "(a slang error, not an x or z finding; a program slang rejects is "
                             "rejected):\n" + lines)
            raise Reject("fourstate", f"an x or z value can arise in the design at {at} "
                         "(ls-sv computes with it, Yosys resolves it as a don't-care, so "
                         "the proved and the scored circuits could differ):\n" + lines)

        # the Python twins of txtask-v2's rules (check/clocked_rules.py), before any Lean stage: early refusals
        # with a message per construct; the statement and the pinned flow stay the authority
        if kind in CLOCKED_KINDS:
            cr = clocked_rules.check(env_path)
            st["clocked_rules"] = cr
            for w in cr["advisories"]:
                res.setdefault("warnings", []).append(f"clocked_rules: {w}")
            if not cr["passed"]:
                raise Reject("clocked_rules", "refused before the proof by a twin of txtask-v2's rules (the "
                             "statement, or the pinned flow, refuses it too):\n" + "\n".join(cr["findings"][:8]))

        lean = Lean(stage, wrap)
        # trusted build
        if build_trusted:
            # the statement's own module too when no library above holds it (a fixture task's Spec)
            smod = task["statement"]["module"]
            extra = [] if smod.split(".")[0] in ("SvGolf", "tasks") else [smod]
            stage_start("trusted", "lake build SvGolf tasks svgolf-eval; seconds when it is up to date, minutes "
                        "after a change of lean-surfaces", wrap)
            rc, out, el = lean.run(["build", "SvGolf", "tasks", "svgolf-eval"] + extra, lake_env=False)
            st["trusted"] = {"exit": rc, "seconds": el}
            if rc != 0:
                note_wait(st["trusted"], lean)
                hint = ("\nThe link of svgolf-eval found `l_LeanModels_Sv_...` references: an "
                        "olean of lean-surfaces' LeanModels.Sv was rewritten outside Lake (without "
                        "the package name). See README.md, \"Building\", for the recovery."
                        if "undefined symbol: l_LeanModels_Sv" in out else
                        "\nThis build is the checker's own, not the submission's: run `lake build` from the "
                        "repository root (README, Building) and fix its first error.")
                raise RuntimeError("`lake build SvGolf tasks svgolf-eval` failed "
                                   f"(infrastructure):\n{tail(out)}{hint}")
            mods_to_build = sorted({m for m in imports if m.startswith("LeanModels.Sv")})
            if mods_to_build:
                rc, out, el = lean.run(["build"] + mods_to_build, lake_env=False)
                if rc != 0:
                    note_wait(st["trusted"], lean)
                    raise Reject("trusted", f"cannot build imported modules {mods_to_build}:\n{tail(out)}")
            note_wait(st["trusted"], lean)

        # the Lean search path, which the tripwire watches (WP-B review: for EVERY solution, and
        # as the search path says, not as the packages directory's listing does)
        search = []
        if not unproved:
            rc, out, el = lean.run(["printenv", "LEAN_PATH"])
            search = search_path_from(out) if rc == 0 else []
            if not search:
                raise RuntimeError("`lake env printenv LEAN_PATH` printed no search path "
                                   f"(infrastructure; exit {rc}; is the project built? {envelope.BUILD_FIRST}):\n"
                                   f"{tail(out)}")

        # package imports (Mathlib and friends, WP-B): the imports alone, compiled first
        pkg = package_imports(imports)
        if pkg:
            bad_names = [m for m in pkg if not MODULE_NAME.fullmatch(m)]
            if bad_names:
                raise Reject("imports", f"not a plain module name (no quoting): {bad_names}")
            absent = packages_missing_from(search, pkg)
            if absent:
                raise RuntimeError(f"the package(s) {absent} are on no entry of the Lean search "
                                   "path (infrastructure: the packages are not built on this "
                                   f"machine, or SVGOLF_LS_ROOT is wrong): {search}")
            revs = package_revisions()
            wrong = revision_mismatches(revs)
            if wrong:
                raise RuntimeError(f"the checkouts of {wrong} are not at the revision the "
                                   f"manifest {manifest_path()} pins (infrastructure: simp sets "
                                   "and lemma names differ between revisions, so the verdict "
                                   f"would depend on the machine): {revs}")
            probe = os.path.join(stage, "Submission", "ImportProbe.lean")
            with open(probe, "w") as fh:
                fh.write(import_probe_text(pkg))
            stage_start("packages", "compiling the solution's package imports alone", wrap)
            rc, out, el = lean.compile(probe)
            st["packages"] = {"imports": sorted(set(pkg)), "exit": rc, "seconds": el,
                              "revisions": revs}
            note_wait(st["packages"], lean)
            verdict = classify_import_probe(pkg, rc, out, search_path=search)
            if verdict and verdict[0] == "reject":
                raise Reject("imports", verdict[1])
            if verdict:
                raise RuntimeError(verdict[1])

        # design (generated, trusted)
        dmod = os.path.join(stage, "Submission", "Design.lean")
        with open(dmod, "w") as fh:
            fh.write(design_module_text(task, env_path, latency))
        stage_start("design", "compiling the generated Submission.Design: load_design_sv2 and the "
                    "unsupported-construct check", wrap)
        rc, out, el = lean.compile(dmod)
        st["design"] = {"exit": rc, "seconds": el}
        note_wait(st["design"], lean)
        if rc != 0 and INFRA_LEAN.search(out):
            raise RuntimeError("the design stage could not run (a missing or unreadable build "
                               "product: rebuild, or wait for a concurrent build, and rerun; "
                               f"this is not a verdict on the design):\n{tail(out)}")
        loud = UNSUPPORTED_AT.search(out) if rc != 0 else None
        if loud:
            raise Reject("design", "the design loads, but ls-sv cannot run it: it contains an "
                         "unsupported construct (`Design2.hasUnsupported`), so no proof about "
                         "it can hold. First one, at " + loud.group(1).strip()[:600] + "\nRewrite "
                         "the design without the construct, or add it to ls-sv by PR "
                         "(README.md, \"Rules\").")
        if rc != 0:
            raise Reject("design", f"the design does not load (ls-sv refused it):\n{errors_first(out)}")
        free = UNSUPPORTED_FREE.search(out)
        if not free:
            raise RuntimeError("the design stage compiled, but its unsupported-construct check "
                               f"printed nothing (infrastructure):\n{tail(out)}")
        st["design"]["unsupported_free_points"] = int(free.group(1))

        if unproved:
            return finish_unproved(res, st, task, sv, env_path, do_score, ps_work, keep, oracle,
                                   lean if tactics else None, postsynth_mode, ppa_mode)

        # solution (timed: the CPU limit, and the wall-clock backstop)
        before = integrity_snapshot(stage, search)
        wall_limit = solution_wall_backstop(limit)
        stage_start("solution", f"compiling Solution.lean, CPU limit {limit:g} s (wall-clock backstop "
                    f"{wall_limit:g} s)", wrap)
        rc, out, el = lean.compile(sol, timeout=wall_limit, cpu_limit=limit, bv_solver=allow_bv, progress=True)
        progress = getattr(lean, "progress", None)
        if rc not in (0, 124) and progress_leaked(out):
            # the progress trace reached the proof (a `#guard_msgs` around a declaration saw it): the compile once more
            # without it, and that verdict stands
            log("solution: the proof saw the progress trace (trace.Kernel); compiling it again without the trace")
            note_wait(st.setdefault("solution", {}), lean)
            rc, out, el = lean.compile(sol, timeout=wall_limit, cpu_limit=limit, bv_solver=allow_bv)
            progress = None
            st["solution"]["progress_retried"] = True
        usage = getattr(lean, "usage", None) or {}
        cpu = usage.get("cpu_s")
        stopped_by = (usage.get("stopped_by") or "wall") if rc == 124 else None
        out = strip_progress(out)
        st["solution"] = dict(st.get("solution") or {}, exit=rc, seconds=el, cpu_seconds=cpu, time_limit_s=limit,
                              time_limit_counts="cpu", wall_limit_s=wall_limit, messages=tail(out, 6000))
        if stopped_by:
            st["solution"]["stopped_by"] = stopped_by
        if progress:
            st["solution"]["progress"] = progress
        note_wait(st["solution"], lean)
        log_solution_time(el, limit, st["solution"].get("waited"), rc, progress, cpu=cpu, wall_limit=wall_limit,
                          stopped_by=stopped_by)
        if rc == 124:
            where = progress_sentence(progress)
            raise Reject("solution", "the proof did not compile within "
                         + solution_timeout_text(limit, wall_limit, el, cpu, stopped_by)
                         + (f"; where the time went: {where}" if where else ""))
        if rc != 0:
            hint = bv_decide_hint(lean_text, out) if not allow_bv else None
            raise Reject("solution", f"the proof does not compile:\n{errors_first(out)}"
                         + (f"\nHINT: {hint}" if hint else ""))

        # integrity (again after scoring, below)
        changed = integrity_diff(before, integrity_snapshot(stage, search))
        st["integrity"] = {"files": len(before), "changed": changed}
        if changed:
            raise Reject("integrity", "trusted files changed while the solution was building "
                         f"(or another build ran concurrently; rerun): {changed[:5]}")

        # comparator
        cargs = ["lean", "--run", COMPARATOR, "--goal", "Submission.Goal",
                 "--solution", "Submission.solution", "--module", "Submission.Solution",
                 "--module", "Submission.Design", "--prefix", "Submission",
                 "--allow", ",".join(task.get("allowed_axioms",
                                               ["propext", "Classical.choice", "Quot.sound"]))]
        if allow_bv:
            cargs.append("--bv-decide")
        goal_arg = LATENCY_DEF if kind in LATENCY_KINDS else None
        if goal_arg is not None:
            cargs += ["--goal-arg", goal_arg]
            if do_score:      # F8: `lat p` at every clocked post-synthesis point, by the kernel (Comparator point 8)
                for p in clocked_points(task):
                    cargs += ["--goal-arg-at", ",".join(str(p[x["name"]]) for x in task["parameters"])]
        vcpu, vwall = verify_limits(vlimit)
        stage_start("comparator", "the kernel checks the theorem against Submission.Goal, the axioms and the "
                    f"dependency closure; CPU limit {vcpu:g} s (wall-clock backstop {vwall:g} s)", wrap)
        rc, out, el = lean.run(cargs, timeout=vwall, cpu_limit=vcpu)
        comp = comparator_report(out, goal_arg)
        st["comparator"] = dict(verify_record(rc, el, vcpu, vwall, getattr(lean, "usage", None)), result=comp)
        note_wait(st["comparator"], lean)
        if rc == 124:
            c = st["comparator"]
            raise Reject("comparator", "the comparator did not finish within " + solution_timeout_text(
                vcpu, vwall, el, c["cpu_seconds"], c["stopped_by"], who="the comparator"))
        if comp is None:
            raise Reject("comparator", f"the comparator did not report:\n{tail(out)}")
        # the imports Lean itself recorded for the compiled solution, against the header the
        # allowlist read (WP-B review: the header reader and Lean must not disagree)
        problem = import_mismatch(imports, (comp.get("imports") or {}).get("Submission.Solution"))
        if problem:
            raise Reject("imports", problem)
        if not comp.get("accepted"):
            raise Reject("comparator", "; ".join(comp.get("errors", [])) or "rejected")
        if goal_arg is not None and do_score:
            res["latency_at"] = latency_at_from_comparator(task, comp, latency)
            st["latency"]["points"] = res["latency_at"]
            st["latency"]["points_from"] = "the kernel: Submission.lat at each point (check/Comparator.lean, point 8)"

        # leanchecker (kernel replay of the submission's modules)
        stage_start("leanchecker", "kernel replay of Submission.Design and Submission.Solution; CPU limit "
                    f"{vcpu:g} s (wall-clock backstop {vwall:g} s)", wrap)
        rc, out, el = lean.run(["leanchecker", "Submission.Design", "Submission.Solution"],
                               timeout=vwall, cpu_limit=vcpu)
        st["leanchecker"] = verify_record(rc, el, vcpu, vwall, getattr(lean, "usage", None))
        note_wait(st["leanchecker"], lean)
        if rc == 124:
            c = st["leanchecker"]
            raise Reject("leanchecker", "kernel replay did not finish within " + solution_timeout_text(
                vcpu, vwall, el, c["cpu_seconds"], c["stopped_by"], who="leanchecker"))
        if rc != 0:
            raise Reject("leanchecker", f"kernel replay failed:\n{tail(out)}")

        # score, postsynth
        if do_score:
            score_and_postsynth(res, st, task, sv, env_path, ps_work, oracle, postsynth_mode,
                                ppa_mode)
        # integrity, once more: nothing changed while the later stages ran
        changed = integrity_diff(before, integrity_snapshot(stage, search))
        st["integrity"]["changed_by_end"] = changed
        if changed:
            raise Reject("integrity", "trusted files changed after the solution was built "
                         f"(or another build ran concurrently; rerun): {changed[:5]}")
        res["accepted"] = True
        res["stage"] = "done"
        incomplete = incomplete_reasons(task, st, do_score, build_trusted, time_limit)
        res["complete"] = not incomplete
        if incomplete:
            res["incomplete"] = incomplete
            log("check: accepted, but the check was INCOMPLETE (no board ranks it): " + "; ".join(incomplete))
    except Reject as r:
        res["stage"] = r.stage
        res["errors"].append(r.msg)
    except score.ScoreError as e:
        res["stage"] = "score"
        res["errors"].append(str(e))
    finally:
        if pol.mode != "off":
            st["sandbox"] = pol.stage_note()
        if ps_work.get("dir"):
            if keep:
                res["postsynth_dir"] = ps_work["dir"]
            else:
                shutil.rmtree(ps_work["dir"], ignore_errors=True)
    return res


# `--tactics`: ONE Lean job, capped like the comparator's would be (it is a few seconds).
TACTICS_TIME_LIMIT_S = 300
# The first line of a Lean error message: `<file>:<line>:<col>: error: <text>`.
LEAN_ERROR = re.compile(r"^.*?:\d+:\d+: error: (.*)$", re.M)


def tactics_probe_text(task, lowered=False):
    """The generated probe of `--tactics`: `sv_structure?` on the goal
    `CombDesign (design.sem N)` that every tactic proof of a combinational
    task starts with (PROVING.md, section 2.1), for the task's parameters (`design.sem W P` for
    two), or `design.sem` for a fixed-size task. With `lowered`, the goal of a design
    with `always_comb` bodies (PROVING.md, section 13): `∃ d', (design.sem N).lowerComb
    = some d' ∧ CombDesign d' ∧ Acyclic d'` with the second elaborator's module
    imported. None for a task that is not combinational (no such task exists
    yet)."""
    kind = task.get("kind")
    params = [p["name"] for p in task.get("parameters", [])]
    if kind == "comb-family" and params:
        # one binder per parameter, in declaration order (`design.sem W P` for a two-parameter task);
        # a name that is not a plain identifier gets `n` (the only parameter) or `n<i>`
        ident = r"[A-Za-z_][A-Za-z0-9_]*"
        vs = [p if re.fullmatch(ident, p) else ("n" if len(params) == 1 else f"n{i}")
              for i, p in enumerate(params)]
        binder = "".join(f" ({v} : Nat)" for v in vs)
        goal = "(design.sem " + " ".join(vs) + ")"
    elif kind == "comb-fixed" and not params:
        binder, goal = "", "design.sem"
    else:
        return None
    imp = "CombProcTactic" if lowered else "CombViewTactic"
    stmt = (f"∃ d', ({goal}).lowerComb = some d' ∧ LeanModels.Sv.CombDesign d' ∧ LeanModels.Sv.Acyclic d'"
            if lowered else f"LeanModels.Sv.CombDesign {goal}")
    return f"""import Submission.Design
import LeanModels.Sv.{imp}

/-!
GENERATED by svgolf/check.py (`--tactics`) for task `{task["name"]}`. Not part of any
submission and compiled by nothing but the pre-check. `sv_structure?` changes nothing and
prints (or refuses, with the reason); the `example` is left unsolved on purpose, the
checker reads the tactic's own message.
-/

namespace Submission

example{binder} : {stmt} := by
  sv_structure?

end Submission
"""


def classify_tactics_output(rc, out):
    """The `tactics` object for the exit status and output of the compiled
    probe. The probe's `example` is left unsolved on purpose, so a design the
    tactic READS ends in `unsolved goals` (and nothing else), and one it
    refuses in the tactic's own error `sv_structure: ...`."""
    errs = [m.group(1).strip() for m in LEAN_ERROR.finditer(out)]
    refusal = next((e for e in errs if e.startswith("sv_structure:")), None)
    if rc == 124:
        return {"in_fragment": None,
                "message": f"the probe did not finish within {TACTICS_TIME_LIMIT_S}s"}
    if refusal:
        return {"in_fragment": False, "message": refusal[:400]}
    if (errs and not all(e.startswith("unsolved goals") for e in errs)) or (not errs and rc):
        first = errs[0] if errs else (out.strip().splitlines() or ["no output"])[-1]
        return {"in_fragment": None, "message": "the probe could not run: " + first[:300]}
    return {"in_fragment": True, "message": "ok"}


def tactics_precheck(res, st, task, lean):
    """`--tactics` (advisory; never changes `accepted`, `stage` or another field):
    one Lean job compiles the generated probe against the staged design.
    `res["tactics"]` = `{"in_fragment": true|false|null, "message": ...}`:
    true/"ok" when `sv_structure?` reads the design, false and the first line of
    its refusal when it does not, null when the probe could not tell (the
    message says why). `st["tactics"]` has the Lean job's seconds (its exit
    status is 1 when the probe's `example` is left unsolved: no information).
    One line on stderr."""
    text = tactics_probe_text(task)
    if text is None:
        res["tactics"] = {"in_fragment": None,
                          "message": f"not checked: task kind {task.get('kind')!r} is not "
                          "a combinational task"}
        log(f"tactics: {res['tactics']['message']}")
        return
    probe = os.path.join(lean.stage, "Submission", "TacticsProbe.lean")
    with open(probe, "w") as fh:
        fh.write(text)
    stage_start("tactics", "sv_structure? on the staged design, advisory", getattr(lean, "wrap", ()))
    rc, out, el = lean.run(["lean", probe], timeout=TACTICS_TIME_LIMIT_S)
    st["tactics"] = {"seconds": el}
    t = res["tactics"] = classify_tactics_output(rc, out)
    if t["in_fragment"] is False:
        # A design with `always_comb` bodies is read by the second elaborator, on the LOWERED goal
        # (PROVING.md, section 13): ask it before saying the design is outside the fragment.
        lprobe = os.path.join(lean.stage, "Submission", "TacticsProbeLowered.lean")
        with open(lprobe, "w") as fh:
            fh.write(tactics_probe_text(task, lowered=True))
        lrc, lout, lel = lean.run(["lean", lprobe], timeout=TACTICS_TIME_LIMIT_S)
        st["tactics"]["lowered_seconds"] = lel
        lt = classify_tactics_output(lrc, lout)
        if lt["in_fragment"] is True:
            t = res["tactics"] = {"in_fragment": True, "lowered": True,
                                  "message": "ok"}
            el += lel
        elif lt["in_fragment"] is False and "procedural process" in t["message"]:
            # the design HAS an `always_comb` the plain tactic cannot read: the second elaborator's
            # refusal (which body construct, which site) is the useful message
            t = res["tactics"] = {"in_fragment": False, "message": lt["message"],
                                  "generic_message": t["message"]}
        else:
            t["lowered_message"] = (lt["message"] if lt["in_fragment"] is False
                                    else "the lowered probe could not run: " + lt["message"])[:400]
    note_wait(st["tactics"], lean)
    log("tactics: " + {True: "inside the sv_comb fragment (sv_structure? reads the design"
                       + (", lowered" if t.get("lowered") else "") + ")",
                       False: "OUTSIDE the sv_comb fragment: " + t["message"],
                       None: t["message"]}[t["in_fragment"]] + f" [{el:.1f} s]")


def note_functional(res, st):
    """The advisory functional smoke check (check/postsynth.py) found a
    mismatch: ONE line in `res["warnings"]`. Nothing else changes."""
    w = postsynth.functional_warning((st.get("postsynth") or {}).get("functional"))
    if w:
        res.setdefault("warnings", []).append(w)


def ppa_reason(e):
    """One line: a PpaError's message with its line breaks and indentation squeezed."""
    return " ".join(str(e).split())


def ppa_block(netlist_path, sres, mode, lib_pins=None, expect_sha256=None, task=None):
    """The `ppa` object for the scored netlist at `netlist_path` (the very file the
    postsynth stage simulated) and the score stage's result `sres`:

      {"available": true, ...score/ppa.py's columns...}     weighed
      {"available": false, "reason": "..."}                  not weighed

    Unweighed means: the pinned liberty is absent, unreadable or not the pinned file (only in
    `auto`; under `require` that is an infrastructure error, RuntimeError), or the pinned flow
    cannot weigh THIS netlist (a cell outside its table, an undriven net, ...: any mode, with
    the loud reason; the design is not at fault for the check), or (sky130_a0_v2, v3) the REPAIRED
    netlist is electrically illegal: then the block also says `"illegal": true` and carries the
    audit's counts (`legality`), and `ppa_stage` REJECTS the design (its fault: decided 11/04). A
    repaired netlist whose function differs from the scored one is a defect of the repair, not of
    the design: nothing is reported (`auto`) or an infrastructure error (`require`). The scored
    netlist's unit depth and gate count (the A0' expansion before the repair, flops included)
    must equal the score stage's `ltp -noff` depth and gate count: a disagreement means the two
    readings of the netlist differ, nothing is reported
    (`auto`) or the run is an infrastructure error (`require`). `expect_sha256`: the sha256 the
    postsynth stage recorded for the netlist it verified (None: not checked); the file read here
    must be those very bytes, else RuntimeError in every mode (the weighed netlist is not the
    verified one: an integrity failure, not a property of the design). `lib_pins`: the opened
    (Liberty, Pins) if the caller has them. `task`: the task.json object, whose `input_drive`
    (sky130_a0_v3; absent: the pins' default) drives every primary input; one the pins do not
    allow is a task-configuration error, RuntimeError in every mode. Pure given the files; no
    state."""
    try:
        lib, pins = lib_pins or ppa.open_library()
    except (ppa.PpaError, OSError) as e:
        if mode == "require":
            raise RuntimeError(f"ppa: {ppa_reason(e)}")
        return {"available": False, "reason": ppa_reason(e)}
    try:
        drive = ppa.input_drive_of(task, pins)
    except ppa.TaskConfigError as e:          # the task's configuration, never the design's
        raise RuntimeError(f"ppa: {ppa_reason(e)}")
    with open(netlist_path, "rb") as fh:
        data = fh.read()
    if expect_sha256 is not None and ppa.sha256_bytes(data) != expect_sha256:
        raise RuntimeError(f"ppa: the netlist file (sha256 {ppa.sha256_bytes(data)}) is not the one the "
                           f"postsynth stage verified (sha256 {expect_sha256}): it changed between the two stages")
    try:
        a = ppa.analyze(data.decode(), lib, pins, input_drive=drive)
    except ppa.IllegalNetlist as e:          # the design's fault: `ppa_stage` rejects it
        return {"available": False, "illegal": True, "reason": ppa_reason(e), "legality": e.summary}
    except ppa.RepairDefect as e:            # the repair's or the reader's fault, not the design's
        why = "the repaired netlist is not the scored circuit: " + ppa_reason(e)
        if mode == "require":
            raise RuntimeError("ppa: " + why)
        return {"available": False, "reason": why}
    except (ppa.PpaError, UnicodeDecodeError) as e:
        return {"available": False, "reason": ppa_reason(e)}
    except Exception as e:   # noqa: BLE001  (a defect of ppa.py must not fail a check; it is reported loudly)
        why = f"ppa.py failed on this netlist: {type(e).__name__}: {ppa_reason(e)}"
        if mode == "require":
            raise RuntimeError("ppa: " + why)
        return {"available": False, "reason": why}
    gates = a.scored_gates
    if a.unit_depth != sres["depth"] or gates != sres["num_gates"]:
        why = (f"the PPA reading of the scored netlist (depth {a.unit_depth}, {gates} gates) differs "
               f"from score.py's (ltp depth {sres['depth']}, {sres['num_gates']} gates)")
        if mode == "require":
            raise RuntimeError("ppa: " + why)
        return {"available": False, "reason": why}
    return dict(ppa.columns(a, pins, lib, ppa.sha256_bytes(data)), available=True)


def ppa_mapped_block(rtlil_path, top, netlist_path, mode, lib_pins=None, expect_rtlil_sha256=None,
                     expect_netlist_sha256=None, mpins=None):
    """The `mapped` object (flow A1', score/ppa.py) of the design whose canonical RTLIL is at `rtlil_path` and whose scored
    netlist, the file the postsynth stage simulated, is at `netlist_path`:

      {"available": true, ...ppa.weigh_mapped's columns...}     mapped and weighed
      {"available": false, "reason": "..."}                      not weighed

    Unweighed means the flow cannot map or weigh THIS design (Yosys fails or times out, a cell outside the policy, a netlist
    the reader or the STA cannot handle, the mapped-flow pins unreadable): any mode, with the loud reason, never a failure of
    the check. A mapped netlist whose FUNCTION differs from the scored one on the equivalence sample is a defect of the flow,
    not of the design: nothing is reported (`auto`) or the run is an infrastructure error (`require`), as is any other
    exception of ppa.py. `expect_rtlil_sha256` / `expect_netlist_sha256`: the hashes the score and postsynth stages recorded
    for the two files (None: not checked); files that are not those bytes are an integrity failure in every mode."""
    try:
        lib, pins = lib_pins or ppa.open_library()
    except (ppa.PpaError, OSError) as e:
        if mode == "require":
            raise RuntimeError(f"ppa: {ppa_reason(e)}")
        return {"available": False, "reason": ppa_reason(e)}
    with open(rtlil_path, "rb") as fh:
        rtlil_sha = ppa.sha256_bytes(fh.read())
    with open(netlist_path, "rb") as fh:
        net = fh.read()
    for what, got, want in (("canonical RTLIL", rtlil_sha, expect_rtlil_sha256),
                            ("netlist file", ppa.sha256_bytes(net), expect_netlist_sha256)):
        if want is not None and got != want:
            raise RuntimeError(f"ppa: the {what} the mapping reads (sha256 {got}) is not the one the score/postsynth stage "
                               f"recorded (sha256 {want}): it changed in between")
    try:
        return ppa.mapped_block(rtlil_path, top, net.decode(), lib, pins, mpins)
    except ppa.MappedDefect as e:
        why = "the mapped netlist is not the scored circuit: " + ppa_reason(e)
    except Exception as e:   # noqa: BLE001  (a defect of ppa.py must not fail a check; it is reported loudly)
        why = f"ppa.py failed on this design's mapping: {type(e).__name__}: {ppa_reason(e)}"
    if mode == "require":
        raise RuntimeError("ppa: " + why)
    return {"available": False, "reason": why}


def ppa_stage(res, st, netlist, sres, ps_work, mode, rtlil=None, top=None, task=None):
    """The `ppa` stage (after `postsynth`, on the netlist it verified): `res["ppa"]` and
    `st["ppa"] = {"mode", "seconds"}`; one line on stderr. With `rtlil` (the canonical RTLIL of the score run, and the task's
    `top`) a weighed block also gets `mapped` (flow A1') and `st["ppa"]["mapped_seconds"]`. Nothing else in the result
    changes. The stage REJECTS (Reject("ppa")) exactly one kind of design: one whose repaired sky130 netlist is electrically
    illegal (a load over max_capacitance, a transition over max_transition, a timing-table read outside its characterized
    range: sky130_a0_v2 and v3 never extrapolate), with the worst cells named; `res["ppa"]` then says why. `task`: the
    task.json object (its `input_drive` drives the primary inputs, sky130_a0_v3)."""
    t0 = time.time()
    block = ppa_block(netlist, sres, mode, ps_work.get("ppa_lib"),
                      (st.get("postsynth") or {}).get("netlist_sha256"), task)
    res["ppa"] = block
    sec = round(time.time() - t0, 2)
    st["ppa"] = {"mode": mode, "seconds": sec}
    if block.get("illegal"):
        log(f"ppa: REJECTED, the repaired sky130 netlist is electrically illegal [{sec} s]")
        raise Reject("ppa", block["reason"])
    if block["available"]:
        log(f"ppa: {block['area_um2_sky130']} um^2, {block['delay_ps_sky130']} ps, "
            f"{block['unit_depth']} levels ({block['ppa_version']}; ranked) "
            f"[{sec} s]")
        if rtlil is not None:
            t1 = time.time()
            block["mapped"] = m = ppa_mapped_block(rtlil, top, netlist, mode, ps_work.get("ppa_lib"),
                                                   sres.get("rtlil_sha256"),
                                                   (st.get("postsynth") or {}).get("netlist_sha256"),
                                                   ps_work.get("ppa_mpins"))
            msec = round(time.time() - t1, 2)
            st["ppa"].update(seconds=round(sec + msec, 2), mapped_seconds=msec)
            if m["available"]:
                log(f"ppa: mapped (A1', real abc -liberty): {m['area_um2_sky130_mapped_v1']} um^2, "
                    f"{m['mapped_delay_sky130_v1']} ps, {m['mapped_cells_sky130_v1']} cells, "
                    f"{m['mapped_levels_sky130_v1']} levels ({m['ppa_mapped_version']}; extra column) "
                    f"[{msec} s]")
            else:
                log(f"ppa: mapped columns not computed: {m['reason']}")
    else:
        log(f"ppa: not computed: {block['reason']}")


def score_and_postsynth(res, st, task, sv, env_path, ps_work, oracle=None, mode=None,
                        ppa_mode="off"):
    """The `score` stage (keeping the scored netlist), the `postsynth`
    stage on that netlist, in `mode` (light or full), and, unless `ppa_mode`
    is "off", the `ppa` stage on the same netlist."""
    stop, sparams = score.task_scoring_point(task)
    if task_kind(task) in CLOCKED_KINDS:
        return score_clocked(res, st, task, sv, env_path, ps_work, oracle, mode, stop, sparams)
    ps_work["dir"] = work = tempfile.mkdtemp(prefix="svgolf-postsynth-")
    netlist = os.path.join(work, "netlist.v")
    t0 = time.time()
    rtlil = os.path.join(work, "canon.il")
    stage_start("score", "the pinned Yosys flow at " + (point_str(sparams) or "the fixed size"))
    sres = score.score([sv], stop, sparams, netlist_out=netlist,
                       rtlil_out=rtlil if ppa_mode != "off" else None)
    budget = task["scoring"].get("depth_budget")
    sres["depth_budget"] = budget
    sres["seconds"] = round(time.time() - t0, 2)
    st["score"] = sres
    res["score"] = {k: sres[k] for k in ("area_ge", "area_mge", "depth", "gates",
                                          "num_gates", "params")}
    if budget is not None and sres["depth"] > budget:
        raise Reject("score", f"depth {sres['depth']} exceeds the task's budget {budget}")
    stage_start("postsynth", "ls-sv against the scored netlist" + (f", {mode} mode" if mode else ""))
    try:
        st["postsynth"] = postsynth.run(task, sv, env_path, netlist, sres, work, oracle=oracle,
                                        mode=mode)
    except postsynth.InfraError as e:
        raise RuntimeError(f"postsynth: {e}")
    except postsynth.Reject as r:
        st["postsynth"] = r.info.get("record")
        note_functional(res, st)
        raise Reject("postsynth", "the post-synthesis check failed: " + r.msg)
    note_functional(res, st)
    ps = st["postsynth"]
    log(f"postsynth: {ps['mode']} mode, {ps['vectors']} vectors "
        + (f"of the full set's {ps['full_vectors']} (local feedback; competitions, `leaderboard.py "
           f"add`/`verify` and tests/run.py run --postsynth full)" if ps["mode"] == "light"
           else "(the task's whole budget)") + f" [{ps['seconds']} s]")
    if ppa_mode != "off":
        ppa_stage(res, st, netlist, sres, ps_work, ppa_mode, rtlil, stop, task)


def never_loaded(sres, sv, top, point):
    """NEVER-LOADED REGISTERS are refused in every clocked task (txtask-v2, decided 2026-11-06), exactly
    where the pinned flow removes a flop while reads of it remain:
    the pinned flow removes a flop whose next value is always its own, or whose enable is never active, and resolves
    each READ of the now undefined value separately, which no single power-up value of the register gives (the
    review's finding A, `ux4_200.sv`). The verdict is the scored run's own log (`score.flop_removals`); the names come
    from a names-kept diagnostic run (`score.undefined_registers`), which also decides whether a constant the log
    prints as "1-bit" was a 1 (one value for every reader: kept) or an x (refused). The same rule covers the memory
    analogue (`score.MEM_UNDEFINED`: an unpacked array's lane no write loads, whose reads opt_mem connects to the
    undefined value before any flop exists), the 2026-11-06 adversarial round's finding F1. Its finding F2, a state
    register the fsm pass re-implements (the new flip-flops power up in codes that are no value of the register), is
    closed by the flow itself (`synth -nofsm`, decided 2026-11-06); `score.FSM_MAPPED` stays as a backstop that should
    never fire. Raises Reject("score")."""
    fr = sres.get("flop_removals") or {}
    if not (fr.get("undefined") or fr.get("constant_one_or_x") or fr.get("memory_undefined") or fr.get("fsm_mapped")):
        return
    diag = score.diagnose_names([sv], top, point)
    names = diag["undefined"]
    more = lambda ls: f" and {len(ls) - 1} more" if len(ls) > 1 else ""  # noqa: E731
    rule = ("Rule (txtask-v2, decided 2026-11-06): in every clocked task, a design is refused where the pinned flow "
            "removes a flip-flop while reads of it remain (its next value is always its own, its enable is never "
            "active, or the only value it is loaded with is undefined), or connects the reads of an array lane no "
            "write loads to an undefined value")
    def register():
        shown = ", ".join(f"`{n}`" for n in names) or "(a register whose name the diagnostic run did not recover)"
        lines = fr.get("undefined") or [ln.replace("1-bit", "x (printed as 1-bit)", 1) for ln in fr["constant_one_or_x"]]
        raise Reject("score", f"never-loaded register at {point_str(point)}: {shown}. The pinned Yosys removes the "
                     f"flip-flop (its log: `{lines[0]}`{more(lines)}) and resolves each read of its now undefined "
                     "value separately, while ls-sv gives a register one power-up value for every read, so the proved "
                     f"and the scored circuits differ. {rule}; reset it, load it with a value other than its own, or "
                     "remove it")
    if fr.get("undefined"):
        register()
    lines = fr.get("memory_undefined") or []
    if lines:
        mems = sorted({m.group(2) for m in map(score.MEM_UNDEFINED.match, lines) if m})
        raise Reject("score", f"never-loaded memory at {point_str(point)}: " + ", ".join(f"`{n}`" for n in mems)
                     + f". No write loads a bit lane of the array with a value, and the pinned Yosys connects every "
                     f"read of that lane to an undefined value before it builds any flip-flop (its log: `{lines[0]}`"
                     f"{more(lines)}), which it resolves separately at each read, while ls-sv gives every word one "
                     f"power-up value for every read, so the proved and the scored circuits differ. {rule}; write the "
                     "lane, or replace the array by constants")
    if fr.get("constant_one_or_x") and names:
        register()
    lines = fr.get("fsm_mapped") or []
    if lines:
        shown = ", ".join(f"`{n}`" for n in diag["fsm"]) or "(a register whose name the diagnostic run did not recover)"
        raise Reject("score", f"state register re-implemented as a state machine at {point_str(point)}: {shown}. The "
                     f"pinned clocked flow runs `synth -nofsm`, yet its log shows Yosys's fsm pass re-encoding the "
                     f"register from the state codes it finds (`{lines[0]}`{more(lines)}): the new flip-flops power up "
                     "in codes that are no value of the register and a value that is no extracted state has no code, "
                     "while ls-sv gives the register one power-up value of its width, so the proved and the scored "
                     "circuits differ from some power-ups. Rule (txtask-v2, 2026-11-06: svGolf disallows a design "
                     "where the pinned Yosys deviates from the semantics): refused in every clocked task. This check "
                     "is a backstop that should never fire: please report the design to the maintainers")


def score_clocked(res, st, task, sv, env_path, ps_work, mod, mode, top, sparams):
    """The clocked `score`, `postsynth` and `ppa` stages (PLAN4 Gate 2 steps 3 and 4; C7): the clocked
    flow (score/svgolf_seq.ys, ge_seq.json) at the scoring point; the clocked post-synthesis check
    (check/postsynth.py `run_clocked`) at each of the task's `postsynth.points` (the scoring point's
    netlist is the scored one, another point's is synthesized by the same flow), a latency kind's
    each against its own latency `lat p` (F8, `latency_at`); the sky130 columns
    of the scored netlist. RANKED: `area_um2` (sky130 A0', flops included) and `time_ps` = `cycles`
    x `period_ps`, the register-to-register period from the pinned liberty (clock-to-Q and setup
    included), `cycles` the declared latency n (1 for a seq-family task: one step per cycle). GE,
    unit depth and the flop count are extra columns."""
    ps_work["dir"] = work = tempfile.mkdtemp(prefix="svgolf-postsynth-")
    t0 = time.time()
    netlist = os.path.join(work, "netlist.v")
    stage_start("score", "the clocked Yosys flow at " + point_str(sparams))
    sres = score.score([sv], top, sparams, netlist_out=netlist, flow="seq")
    sres["seconds"] = round(time.time() - t0, 2)
    st["score"] = sres
    never_loaded(sres, sv, top, sparams)
    points = clocked_points(task)       # the scored netlist is always checked
    lat_at = res.get("latency_at") or {}

    def latency_of(pt):
        """The latency the check uses at `pt` (F8): `lat pt` (a proved run: the kernel's; `--unproved`: the command
        line's), or None for a kind without one."""
        if res.get("latency") is None:
            return None
        if point_str(pt) not in lat_at:
            raise RuntimeError(f"no latency for the clocked post-synthesis point {point_str(pt)} (infrastructure)")
        return lat_at[point_str(pt)]
    stage_start("postsynth", f"the clocked check, ls-sv against the netlist cycle by cycle, at {len(points)} "
                "point(s)" + (f", {mode} mode" if mode else "")
                + ("; latency " + ", ".join(f"{latency_of(p)} at {point_str(p)}" for p in points)
                   if res.get("latency") is not None else ""))
    st["postsynth"] = {"points": []}
    try:
        for k, pt in enumerate(points):
            nl, pres = netlist, sres
            if pt != sparams:
                nl = os.path.join(work, f"netlist_{k}.v")
                pres = score.score([sv], top, pt, netlist_out=nl, flow="seq")
                never_loaded(pres, sv, top, pt)
            pw = os.path.join(work, f"point_{k}")
            os.makedirs(pw)
            st["postsynth"]["points"].append(postsynth.run_clocked(
                task, env_path, nl, pres, pw, mod, pt, latency_of(pt), mode))
    except postsynth.InfraError as e:
        raise RuntimeError(f"postsynth: {e}")
    except postsynth.Reject as r:
        st["postsynth"]["points"].append(r.info.get("record"))
        raise Reject("postsynth", "the clocked post-synthesis check failed: " + r.msg)
    st["postsynth"]["netlist_sha256"] = st["postsynth"]["points"][points.index(sparams)]["netlist_sha256"]
    ppa_stage(res, st, netlist, sres, ps_work, "require", task=task)
    cycles = res.get("latency") or 1
    p = res["ppa"]
    if not p.get("available"):       # the ranked clocked score IS this block: without it there is no score
        raise RuntimeError(f"ppa: the clocked score needs the sky130 columns, which were not computed: {p.get('reason')}")
    res["score"] = {"area_um2": p["area_um2_sky130"], "period_ps": p["delay_ps_sky130"], "cycles": cycles,
                    "time_ps": cycles * p["delay_ps_sky130"], "ranked": ["area_um2", "time_ps"],
                    **{k: sres[k] for k in ("area_ge", "area_mge", "depth", "ffs", "gates", "num_gates",
                                            "params")}}
    log(f"score (clocked, C7): {res['score']['area_um2']} um^2, {cycles} x {p['delay_ps_sky130']} ps = "
        f"{res['score']['time_ps']} ps; extra: {sres['area_ge']} GE, unit depth {sres['depth']}, "
        f"{sres['ffs']} flops; postsynth at {len(points)} point(s) [{round(time.time() - t0, 2)} s]")


def finish_unproved(res, st, task, sv, env_path, do_score, ps_work, keep, oracle=None,
                    tactics_lean=None, postsynth_mode=None, ppa_mode="off"):
    """`--unproved`: the stages after `design` that need no proof, then stop.
    With `tactics_lean` (the `Lean` runner of the staging tree), first the
    advisory fragment pre-check (`--tactics`)."""
    try:
        if tactics_lean is not None:
            tactics_precheck(res, st, task, tactics_lean)
        if do_score:
            score_and_postsynth(res, st, task, sv, env_path, ps_work, oracle, postsynth_mode,
                                ppa_mode)
        res["stage"] = "unproved"
        # a CLEAN run (exit status 0): nothing failed, so the sentence is a note, not an error; `accepted` stays false
        res.setdefault("notes", []).append("--unproved: every check that needs no proof passed (source, "
                                           "extract, banlist, fourstate, design"
                                           + (", score, postsynth" if do_score else "")
                                           + "); the proof stages were not run, so the design is not accepted")
        res["unproved_ok"] = True
    except Reject as r:
        res["stage"] = r.stage
        res["errors"].append(r.msg)
    except score.ScoreError as e:
        res["stage"] = "score"
        res["errors"].append(str(e))
    return res


def dev_hint(stage, wrap, unproved, res):
    """`{"dev_hint": command}` for a run that keeps its staging directory, or
    `{}`. The command is the one `Lean.run` would run, the Lean wrapper (`wrap`,
    `--lean-wrap` / $SVGOLF_LEAN_WRAP) in front of `lake` exactly as there, so on
    a shared machine it goes through the slot wrapper too.
      full run     recompile the submission's `Solution.lean` against the staged
                   design;
      `--unproved` (no `Solution.lean` yet) compile ANY probe file against the
                   staged design (`<YourFile>.lean`, a literal placeholder: it
                   starts with `import Submission.Design`). Only when the
                   `design` stage compiled `Submission.Design`: before that
                   there is nothing to compile against."""
    prefix = "".join(shlex.quote(w) + " " for w in wrap)
    head = f"cd {SVGOLF} && LEAN_PATH={os.path.join(stage, 'build')} {prefix}lake env lean "
    if not unproved:
        return {"dev_hint": head + os.path.join(stage, "Submission", "Solution.lean")}
    if res.get("stages", {}).get("design", {}).get("exit") != 0:
        return {}
    return {"dev_hint": head + "<YourFile>.lean   # compiles any probe file against the staged "
            "design; the file starts with `import Submission.Design`"}


# SVGOLF_LEAN_WRAP_ONCE (item 9 of the newcomer study): the wrapper taken once, around a re-run of check.py whose
# environment carries the wrapper in HELD (so that it calls lake and lean directly, and its `dev_hint` still puts the
# wrapper in front of lake) and the time the outer run asked for it in SINCE.
LEAN_WRAP_ONCE_ENV = "SVGOLF_LEAN_WRAP_ONCE"
LEAN_WRAP_HELD_ENV = "SVGOLF_LEAN_WRAP_HELD"
LEAN_WRAP_SINCE_ENV = "SVGOLF_LEAN_WRAP_SINCE"


def lean_wrap_plan(wrap, environ):
    """How this run uses the Lean wrapper `wrap` (a list; `--lean-wrap` / $SVGOLF_LEAN_WRAP): a dict with `mode`,
    `call` (the prefix of each lake/lean call), `hint` (the one `dev_hint` shows) and `since` (inside: when the outer
    run asked for the wrapper, or None). Pure.
      inside    this run IS the one behind the wrapper (HELD is set): calls go direct, the hint keeps the wrapper;
      once      $SVGOLF_LEAN_WRAP_ONCE=1 and a wrapper: re-run check.py behind it, once;
      per-call  a wrapper in front of every lake/lean call (the default);
      none      no wrapper."""
    held = environ.get(LEAN_WRAP_HELD_ENV)
    if held is not None:
        try:
            since = float(environ.get(LEAN_WRAP_SINCE_ENV, ""))
        except ValueError:
            since = None
        return {"mode": "inside", "call": [], "hint": held.split(), "since": since}
    if wrap and environ.get(LEAN_WRAP_ONCE_ENV) == "1":
        return {"mode": "once", "call": list(wrap), "hint": list(wrap), "since": None}
    return {"mode": "per-call" if wrap else "none", "call": list(wrap), "hint": list(wrap), "since": None}


def run_once_behind_wrapper(wrap, argv):
    """$SVGOLF_LEAN_WRAP_ONCE=1: this check.py, with the same arguments, behind the wrapper ONCE (one queue
    entry, one slot for the whole run); its stdout, stderr and exit status are this run's."""
    env = dict(os.environ)
    env[LEAN_WRAP_HELD_ENV] = " ".join(wrap)
    env[LEAN_WRAP_SINCE_ENV] = repr(time.time())
    log(f"check: lean wrapper ... (taken once for the whole run, {LEAN_WRAP_ONCE_ENV}=1: it may queue first)")
    try:
        rc = subprocess.run(wrap + [sys.executable, os.path.abspath(__file__)] + list(argv), env=env).returncode
    except OSError as e:
        print(json.dumps({"accepted": False, "stage": "infrastructure",
                          "errors": [f"the Lean wrapper {' '.join(wrap)!r} cannot be started: {e}"]}, indent=2))
        return 2
    except KeyboardInterrupt:
        return 130
    return rc if rc >= 0 else 128 - rc


def _load_by_path(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def liberty_problem():
    """Why the pinned liberty cannot be opened (score/ppa.py), or None."""
    try:
        ppa.open_library()
    except (ppa.PpaError, OSError) as e:
        return ppa_reason(e)
    return None


def task_par(task_name):
    """(par row, None) of the task as `leaderboard.py board` shows it (leaderboard.py `par_now`: the reference
    player's records in leaderboard/data), (None, None) when there is none, (None, why) when it cannot be read.
    Advisory: it never touches the verdict."""
    try:
        lb = _load_by_path("svgolf_leaderboard_par", os.path.join(SVGOLF, "leaderboard", "leaderboard.py"))
        return lb.par_now(task_name), None
    except Exception as e:   # noqa: BLE001  (the headline is advice; a broken leaderboard must not break a check)
        return None, f"{type(e).__name__}: {' '.join(str(e).split())[:200]}"


def ranked_headline(res):
    """The last stderr line of a run that reached the `ppa` stage (None for any other run): the ranked number,
    area x time (leaderboard/combined.py), against par (`task_par`)."""
    if "ppa" not in (res.get("stages") or {}):
        return None
    block = res.get("ppa") or {}
    if not block.get("available"):
        if not block.get("illegal") and liberty_problem() is not None:
            return "ranked: liberty missing, run python3.12 score/ppa.py --fetch-liberty"
        return "ranked: not computed: " + " ".join(str(block.get("reason", "?")).split())[:300]
    comb = _load_by_path("svgolf_combined_headline", os.path.join(SVGOLF, "leaderboard", "combined.py"))
    sc = res.get("score") or {}
    time_ps = sc["time_ps"] if "time_ps" in sc else block.get("delay_ps_sky130")     # clocked: cycles x period
    exact = comb.of_columns(area_e4um2=block.get("area_e4um2_sky130"), time=time_ps)
    if exact is None:
        return "ranked: not computed: the sky130 columns carry no area or time"
    line = f"ranked (sky130 A0'): {block['area_um2_sky130']} um^2 x {time_ps} ps = {comb.um2ns(exact):.2f} um2*ns"
    par, why = task_par(res.get("task"))
    if par is not None:
        return line + f"; par {par['um2ns']:.2f} ({par['name']})"
    return line + ("; par: none recorded" if why is None else f"; par: unavailable ({why})")


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv[:1] == ["--_timed"]:
        return timed_main(argv[1:])
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("task_dir")
    ap.add_argument("solution_sv")
    ap.add_argument("solution_lean", nargs="?")
    ap.add_argument("--json", help="also write the result JSON here")
    ap.add_argument("--stage-dir", help="staging directory (default: a fresh temp dir)")
    ap.add_argument("--keep", action="store_true", help="keep the staging directory")
    ap.add_argument("--lean-wrap", default=os.environ.get("SVGOLF_LEAN_WRAP", ""))
    ap.add_argument("--sandbox", choices=sandbox.MODES, default=os.environ.get("SVGOLF_SANDBOX", "auto"),
                    help="run every process that touches submitted text (Lean, the extractor, Yosys, Verilator, "
                    "the compiled model) under the OS sandbox: macOS Seatbelt, Linux bubblewrap (README.md, "
                    "\"Sandbox\"). `auto` (default, $SVGOLF_SANDBOX) uses it when the mechanism exists and "
                    "passes its self-test and says on stderr when it does not; `require` makes that an "
                    "infrastructure error (competitions, `leaderboard.py add`/`verify`); `off` runs without it "
                    "(the environment is scrubbed in every mode)")
    ap.add_argument("--time-limit", type=float, help="override the task's time limit: the CPU seconds of the "
                    "solution's compile (its wall-clock backstop is SOLUTION_WALL_FACTOR times it)")
    ap.add_argument("--postsynth", choices=postsynth.MODES,
                    help="the post-synthesis mode: `light` (a deterministic subset of the vectors, "
                    "for local feedback) or `full` (the task's whole budget: competitions, "
                    "verification and the leaderboard run this). Default: $SVGOLF_POSTSYNTH, "
                    "else light")
    ap.add_argument("--ppa", choices=PPA_MODES, default="auto",
                    help="the sky130 PPA columns (score/ppa.py): flow A0' is the ranked score of the "
                    "default board (its area x delay is the one number par is measured in), flow A1' "
                    "(the `mapped` sub-object, a real `abc -liberty` mapping of the canonical RTLIL) "
                    "an extra column. `auto` (default) weighs the scored netlist when the pinned "
                    "liberty is present and records `ppa: {available: false, reason}` when it is "
                    "not; `require` makes an absent liberty an infrastructure error (official "
                    "runs); `off` adds no key and no stage (and the result cannot be ranked)")
    ap.add_argument("--latency", type=int,
                    help="with --unproved, for a tx-family or stream-family task: the latency n the goal pins at the "
                    "scoring point (a proved run reads it from the solution's `-- svgolf-latency:` line)")
    ap.add_argument("--latency-at", action="append", metavar="POINT:N",
                    help="with --unproved and --latency (repeatable): the latency at another point of the clocked "
                    "post-synthesis check, e.g. N=3,W=4:6; a point not named is checked against --latency (a proved "
                    "run asks the kernel for the solution's `Submission.lat` at every point)")
    ap.add_argument("--no-score", action="store_true")
    ap.add_argument("--no-trusted-build", action="store_true",
                    help="skip `lake build SvGolf tasks svgolf-eval` (when it is known to be "
                    "up to date)")
    ap.add_argument("--unproved", action="store_true",
                    help="no Lean file: every check that needs no proof, never accepted")
    ap.add_argument("--tactics", action="store_true",
                    help="with --unproved: also ask the sv_comb tactics (`sv_structure?`, one "
                    "extra Lean job) whether they can read the design at all; advisory: the "
                    "result's `tactics` says in_fragment true/false and why, nothing else changes")
    args = ap.parse_args(argv)
    if args.unproved != (args.solution_lean is None):
        ap.error("give Solution.lean (the proof), or --unproved without one")
    if args.tactics and not args.unproved:
        ap.error("--tactics is a pre-check for --unproved runs (before a proof exists)")
    try:
        latency_at = parse_latency_at(args.latency_at)
    except ValueError as e:
        ap.error(str(e))
    for p in (args.task_dir, args.solution_sv) + ((args.solution_lean,) if args.solution_lean
                                                  else ()):
        if not os.path.exists(p):
            ap.error(f"no such file or directory: {p}")
    if not os.path.isfile(os.path.join(args.task_dir, "task.json")):
        ap.error(f"{args.task_dir} is not a task directory (it has no task.json): give tasks/<name>")
    try:
        pmode = postsynth.resolve_mode(args.postsynth)
    except postsynth.InfraError as e:
        ap.error(str(e))
    plan = lean_wrap_plan(args.lean_wrap.split(), os.environ)
    if plan["mode"] == "once":
        return run_once_behind_wrapper(plan["call"], argv)
    if os.environ.get(LEAN_WRAP_ONCE_ENV) == "1" and plan["mode"] == "none":
        log(f"check: {LEAN_WRAP_ONCE_ENV}=1 does nothing without a Lean wrapper (SVGOLF_LEAN_WRAP or --lean-wrap)")
    wrap = plan["call"]
    once_waited = None
    if plan["mode"] == "inside" and plan["since"] is not None:
        once_waited = round(max(0.0, time.time() - plan["since"]), 2)
        log(f"check: the Lean wrapper let this run start after {once_waited:.1f} s")
    try:
        sandbox.configure(args.sandbox, log=log)     # detect, self-test, say so on stderr
    except sandbox.Unavailable as e:
        print(json.dumps({"accepted": False, "stage": "infrastructure", "errors": [str(e)],
                          "sandbox": {"mode": args.sandbox, "mechanism": None, "active": False}}, indent=2))
        return 2
    stage = os.path.realpath(args.stage_dir if args.stage_dir else
                             tempfile.mkdtemp(prefix="svgolf-check-"))
    if args.stage_dir and os.path.exists(stage):
        shutil.rmtree(stage)
    os.makedirs(stage, exist_ok=True)
    try:
        res = check(os.path.abspath(args.task_dir), os.path.abspath(args.solution_sv),
                    args.solution_lean and os.path.abspath(args.solution_lean), stage,
                    wrap, args.time_limit, not args.no_score,
                    not args.no_trusted_build, args.unproved, args.keep or bool(args.stage_dir),
                    args.tactics, pmode, args.ppa, args.latency, latency_at)
    except RuntimeError as e:
        print(json.dumps({"accepted": False, "stage": "infrastructure", "errors": [str(e)]},
                         indent=2))
        return 2
    finally:
        if not args.keep and not args.stage_dir:
            shutil.rmtree(stage, ignore_errors=True)
        sandbox.policy().close()
    if plan["mode"] == "inside":
        res["lean_wrap"] = {"once": True, "waited": once_waited}
    if args.keep or args.stage_dir:
        res.update(dev_hint(stage, plan["hint"], args.unproved, res))
    if args.unproved:
        for w in res.get("warnings", []):
            log(w)     # the same advisory line as in the JSON's `warnings`
    text = json.dumps(res, indent=2, sort_keys=True)
    print(text)
    if args.json:
        with open(args.json, "w") as fh:
            fh.write(text + "\n")
    try:
        headline = ranked_headline(res)
    except Exception as e:   # noqa: BLE001  (advice on stderr: never a crash after the verdict is printed)
        headline = f"ranked: not computed: {type(e).__name__}: {e}"
    if headline:
        log(headline)     # the LAST line on stderr (contract: the ranked headline)
    # 0: accepted, or a clean `--unproved` run (every stage it runs passed); 1: a stage failed
    return 0 if res["accepted"] or res.get("unproved_ok") else 1


if __name__ == "__main__":
    sys.exit(main())
