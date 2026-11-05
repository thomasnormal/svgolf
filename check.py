#!/usr/bin/env python3.12
"""svGolf checker v0: check one submission against one task, then score it.

    python3.12 check.py TASK_DIR SOLUTION.sv SOLUTION.lean [--json OUT]
    python3.12 check.py TASK_DIR DESIGN.sv --unproved      # every check but the proof
    python3.12 check.py TASK_DIR DESIGN.sv --unproved --tactics   # ... and can the tactics read it?

A submission is a SystemVerilog file and a Lean file. The Lean file proves

    theorem Submission.solution : Submission.Goal

where `Submission.Goal` is the task's statement about the design that the
checker extracts from SOLUTION.sv (README.md, "Submitting"). Stages, in
order; the first failing stage rejects:

  task          read TASK_DIR/task.json; its `kind` (`KINDS`): combinational, or CLOCKED
                (`seq-family`, `tx-family`, PLAN4 Gate 2; `stream-family`, C8: the task
                names its `clock`; its score, postsynth and ppa stages are the clocked
                ones, `score_clocked`)
  latency       (tx-family, stream-family: `LATENCY_KINDS`) the solution's one header
                line `-- svgolf-latency: n`
                (n ≥ 1); the goal is then `Goal lat := Statement design.sem lat ∧
                lat p₀ = n` for the solution's definition `Submission.lat`, and the
                result records `latency: n`. Any other kind refuses the line
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
  banlist       score/banlist.py: pyslang front check + Yosys backstop
  fourstate     score/fourstate.py, at the scoring point: no x or z value can
                arise (no parameter or constant expression with unknown bits,
                no constant or run-time select that can leave its range, no
                undriven or conflicting net, no logic loop: Yosys `check`).
                ls-sv computes with x as IEEE 1800 does, Yosys resolves it as
                a don't-care, so every source of x is refused exactly (the
                x/z LITERALS are the source gate's)
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
  solution      compile SOLUTION.lean as `Submission.Solution`, under the
                task's wall-clock limit
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
                replayed through the kernel (under a time limit)
  leanchecker   kernel replay of the submission's modules (environment
                hacking; under a time limit)
  score         score/score.py at the task's scoring point (the two-stage
                canonical flow), keeping the scored gate netlist
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
                instead (`run_clocked`: randomized start state, reset, the task's
                oracle.py transactions, ls-sv `--trace` vs the netlist cycle by
                cycle, the oracle's result binding) at each `postsynth.points`
  ppa           score/ppa.py (WP-X3): the EXTRA sky130 columns of the very
                netlist the score stage kept and postsynth verified (area in
                um^2, delay in ps, unit depth, cell histogram, with the inputs'
                hashes), as the result key `ppa`; the default board (area_ge_v1,
                depth_v1) and every other field are untouched. `--ppa {auto,off,
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
                design it cannot map (never a failure of the check); neither flow
                is official. `--ppa` semantics are unchanged

Prints the result JSON (`accepted`, `stage`, `errors`, per-stage details,
`score`, and `ppa` unless `--ppa off`). Exit status: 0 accepted, 1 rejected,
2 usage or infrastructure error.

`--unproved` (no Lean file) runs every stage that does not need a proof
(source, extract, banlist, fourstate, trusted, design, score, postsynth, ppa) and NEVER
accepts: a design that passes them all stops at the pseudo-stage `unproved`.
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
                    slot-limiting wrapper); --lean-wrap overrides
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
import hashlib
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
import time

sys.dont_write_bytecode = True
SVGOLF = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(SVGOLF, "score"))
sys.path.insert(0, os.path.join(SVGOLF, "check"))
import banlist  # noqa: E402
import envelope  # noqa: E402  (check/envelope.py: the one extraction path)
import layout  # noqa: E402  (check/layout.py: where lean-surfaces is, in either layout)
import fourstate  # noqa: E402  (score/fourstate.py: no x or z value can arise)
import postsynth  # noqa: E402  (check/postsynth.py: the post-synthesis check)
import sandbox  # noqa: E402  (check/sandbox/: the environment scrub, the sandbox, WP-S)
import ppa  # noqa: E402  (score/ppa.py: the extra sky130 PPA columns, WP-X3)
import score  # noqa: E402
from envelope import parse_point, point_str, probe_points  # noqa: E402,F401

LS_ROOT = envelope.LS_ROOT
LAYOUT = envelope.LAYOUT      # "inside" lean-surfaces or "standalone" (check/layout.py)
EXTRACTOR = envelope.EXTRACTOR
ENVELOPE_PY = os.path.join(SVGOLF, "check", "envelope.py")
COMPARATOR = os.path.join(SVGOLF, "check", "Comparator.lean")
SVEVAL_SRC = os.path.join(SVGOLF, "check", "SvEval.lean")
# Wall-clock limit for each of the comparator and leanchecker (they run no
# submission code, but a submission can make kernel checking slow).
VERIFY_TIME_LIMIT_S = 900
# The wall-clock limit of a sandboxed Lean run that has no task limit (the generated design module, the
# import probe, `--tactics`): they run no player proof, but they run on the player's design.
LEAN_DEFAULT_WALL_S = 900
# The `--ppa` modes (score/ppa.py columns; the default board never depends on them).
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


def log(*a):
    print(*a, file=sys.stderr, flush=True)


# ---------------------------------------------------------------------------
# a timed child process (the wall-clock limit excludes waiting for the wrapper)
# ---------------------------------------------------------------------------

def timed_main(argv):
    """`check.py --_timed WALL_S [limits] -- COMMAND...`: the supervisor (check/sandbox/supervisor.py), which
    enforces the wall-clock limit (excluding the wait in a slot wrapper in front of it) and, for a sandboxed
    command, the memory, output and file-size limits, from OUTSIDE the sandbox."""
    return sandbox.supervisor.main(argv)


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

# The line the supervisor prints on stderr when its command ends (see Lean.run):
# `SVGOLF_ELAPSED <s> peak_rss_mb=<n> out_bytes=<n> verdict=<none|memory|output>`.
ELAPSED_LINE = re.compile(r"SVGOLF_ELAPSED ([\d.]+)([^\n]*)\n?")


def split_status(out):
    """(`out` without the supervisor's lines, the elapsed seconds or None, the genuine line's
    `key=value` fields). The genuine reading is the LAST line (the supervisor prints it after the
    command has ended), so a solution that prints the same words cannot forge it; none of these
    lines ever reaches an error message or the result JSON."""
    ms = ELAPSED_LINE.findall(out)
    fields = dict(kv.split("=", 1) for kv in ms[-1][1].split() if "=" in kv) if ms else {}
    return ELAPSED_LINE.sub("", out), float(ms[-1][0]) if ms else None, fields


def split_elapsed(out):
    """(`out` without the supervisor's lines, the elapsed seconds or None): `split_status` without
    the fields."""
    clean, elapsed, _ = split_status(out)
    return clean, elapsed


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

    def _env(self):
        env = sandbox.scrubbed_env()
        env["LEAN_PATH"] = self.build + (":" + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
        return env

    def _capture_lake_env(self):
        """(search path, sysroot) from `lake env` (LEAN_PATH, LEAN_SYSROOT), once, unsandboxed."""
        if self._lake_env is None:
            # (`printenv` takes one name on macOS: ask a shell for both)
            proc = subprocess.run(self.wrap + ["lake", "env", "sh", "-c",
                                               'printf "%s\\n%s\\n" "$LEAN_PATH" "$LEAN_SYSROOT"'],
                                  cwd=SVGOLF, env=self._env(), capture_output=True, text=True)
            lines = [ln.strip() for ln in (proc.stdout).splitlines() if ln.strip()]
            if proc.returncode != 0 or len(lines) < 2 or not os.path.isdir(lines[-1]):
                raise RuntimeError("`lake env` gave no LEAN_PATH or LEAN_SYSROOT "
                                   f"(infrastructure; exit {proc.returncode}):\n{tail(proc.stdout + proc.stderr)}")
            self._lake_env = ([p for p in lines[-2].split(":") if p], lines[-1])
        return self._lake_env

    def run(self, args, timeout=None, lake_env=True, bv_solver=False):
        pol = sandbox.policy()
        if pol.active and lake_env:
            if args[:2] == ["printenv", "LEAN_PATH"]:
                t0 = time.time()
                path, _ = self._capture_lake_env()
                return 0, ":".join(path) + "\n", round(time.time() - t0, 2)
            if args[0] in ("lean", "leanchecker"):
                return self._run_sandboxed(args, timeout, bv_solver)
        if pol.active:
            pol.unsandboxed("lake build (trusted modules only)" if not lake_env else "lake env " + args[0])
        # an ALLOWLISTED environment (check/sandbox/envscrub.py): the competition salt and the
        # checker's other secrets never reach a process that runs the submission's Lean
        env = self._env()
        inner = (["lake", "env"] if lake_env else ["lake"]) + args
        if timeout:
            inner = [sys.executable, os.path.abspath(__file__), "--_timed", str(timeout), "--"] + inner
        t0 = time.time()
        proc = subprocess.run(self.wrap + inner, cwd=SVGOLF, env=env, capture_output=True,
                              text=True)
        out = proc.stdout + proc.stderr
        # the elapsed-time line is parsed here and removed from the text
        out, elapsed = split_elapsed(out)
        return proc.returncode, out, round(time.time() - t0, 2) if elapsed is None else elapsed

    def _run_sandboxed(self, args, timeout, bv_solver=False):
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
        sup = [sys.executable, "-S", "-B", sandbox.SUPERVISOR, str(wall), "--rss-mb", str(lim["rss_mb"]),
               "--out-mb", str(lim["out_mb"]), "--fsize-mb", str(lim["fsize_mb"]), "--cpu-s", str(lim["cpu_s"]),
               "--merge", "--cwd", self.stage, "--forward-env", "LEAN_NUM_THREADS", "--"] + argv   # the slot's thread budget
        t0 = time.time()
        proc = subprocess.run(self.wrap + sup, cwd=SVGOLF, env=sandbox.scrubbed_env(), capture_output=True,
                              text=True, errors="replace")
        out, elapsed, fields = split_status(proc.stdout + proc.stderr)
        if fields.get("peak_rss_mb"):
            pol.note["peak_rss_mb"] = max(pol.note.get("peak_rss_mb", 0), int(fields["peak_rss_mb"]))
        if adopt:
            self._adopt_output(*adopt, outdir)
        return proc.returncode, out, round(time.time() - t0, 2) if elapsed is None else elapsed

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

    def compile(self, module_path, timeout=None, bv_solver=False):
        rel = os.path.relpath(module_path, self.stage)
        olean = os.path.join(self.build, os.path.splitext(rel)[0] + ".olean")
        os.makedirs(os.path.dirname(olean), exist_ok=True)
        return self.run(["lean", "-R", self.stage, "-o", olean, module_path], timeout=timeout,
                        bv_solver=bv_solver)


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
# `protocol` names the stream ports and the parameter that is the number of values (`count`).
KINDS = ("comb-family", "comb-fixed", "seq-family", "tx-family", "stream-family")
CLOCKED_KINDS = ("seq-family", "tx-family", "stream-family")
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

def check(task_dir, sv_path, lean_path, stage, wrap, time_limit=None, do_score=True,
          build_trusted=True, unproved=False, keep=False, tactics=False, postsynth_mode=None,
          ppa_mode="auto", latency=None):
    """Check one submission. With `unproved` (and `lean_path` None), run every
    stage that needs no proof and stop at the pseudo-stage `unproved`, never
    accepting; with `tactics` (only then), also run the advisory fragment
    pre-check after the `design` stage. With `keep`, the postsynth work
    directory (netlist, vectors, simulator outputs) is kept and named in the
    result. `postsynth_mode` is "light" or "full" (None: `$SVGOLF_POSTSYNTH`,
    else light; check/postsynth.py, "TWO MODES"); the result's
    `stages.postsynth.mode` says which ran. `ppa_mode` is "auto", "off" or
    "require" (the `ppa` stage, below): "require" opens the pinned liberty NOW,
    before any work, and an absent or wrong file is an infrastructure error."""
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
            oracle = postsynth.clocked_oracle(oracle)
        if (latency is not None) != (unproved and kind in LATENCY_KINDS):
            raise RuntimeError("--latency is given exactly for an --unproved run of a tx-family or stream-family task "
                               "(a proved run reads it from the solution's header)")
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

        # banlist (on the canonical text, which the gate already checked)
        ops, points = banlist.task_banlist(task)
        if ops:
            front, diags = banlist.front_check([sv], top, ops, probe_pts + points)
            back = banlist.backstop_check([sv], top, ops, points)
        else:
            front, diags, back = [], [], []
        front, back, diags = ([f.replace(sv, shown) for f in xs] for xs in (front, back, diags))
        st["banlist"] = {"operators": ops, "front": front, "backstop": back,
                         "diagnostics": diags}
        if front or back or diags:
            raise Reject("banlist", "banned run-time operators (or the design does not "
                         f"elaborate): {(front + back + diags)[:6]}")

        # fourstate (at the scoring point: the design that is scored)
        try:
            fs = fourstate.check([sv], *score.task_scoring_point(task))
        except fourstate.InfraError as e:
            raise RuntimeError(f"fourstate: {e}")
        fs["findings"] = [f.replace(os.path.realpath(sv), shown).replace(sv, shown)
                          for f in fs["findings"]]
        fs["diagnostics"] = [f.replace(os.path.realpath(sv), shown).replace(sv, shown)
                             for f in fs["diagnostics"]]
        st["fourstate"] = fs
        if not fs["passed"]:
            lines = "\n".join((fs["findings"] + fs["diagnostics"])[:8])
            if fs["diagnostics"]:
                # slang's own errors: a program slang reports illegal is rejected, and any finding listed with
                # them comes from slang's error recovery (WP-RB1: a slang error is not an x/z finding)
                raise Reject("fourstate", "slang reports the program illegal at the scoring point "
                             "(a slang error, not an x or z finding; a program slang rejects is "
                             "rejected):\n" + lines)
            raise Reject("fourstate", "an x or z value can arise in the design at the scoring "
                         "point (ls-sv computes with it, Yosys resolves it as a don't-care, so "
                         "the proved and the scored circuits could differ):\n" + lines)

        lean = Lean(stage, wrap)
        # trusted build
        if build_trusted:
            # the statement's own module too when no library above holds it (a fixture task's Spec)
            smod = task["statement"]["module"]
            extra = [] if smod.split(".")[0] in ("SvGolf", "tasks") else [smod]
            rc, out, el = lean.run(["build", "SvGolf", "tasks", "svgolf-eval"] + extra, lake_env=False)
            st["trusted"] = {"exit": rc, "seconds": el}
            if rc != 0:
                hint = ("\nThe link of svgolf-eval found `l_LeanModels_Sv_...` references: an "
                        "olean of lean-surfaces' LeanModels.Sv was rewritten outside Lake (without "
                        "the package name). See README.md, \"Building\", for the recovery."
                        if "undefined symbol: l_LeanModels_Sv" in out else "")
                raise RuntimeError("`lake build SvGolf tasks svgolf-eval` failed "
                                   f"(infrastructure):\n{tail(out)}{hint}")
            mods_to_build = sorted({m for m in imports if m.startswith("LeanModels.Sv")})
            if mods_to_build:
                rc, out, el = lean.run(["build"] + mods_to_build, lake_env=False)
                if rc != 0:
                    raise Reject("trusted", f"cannot build imported modules {mods_to_build}:\n{tail(out)}")

        # the Lean search path, which the tripwire watches (WP-B review: for EVERY solution, and
        # as the search path says, not as the packages directory's listing does)
        search = []
        if not unproved:
            rc, out, el = lean.run(["printenv", "LEAN_PATH"])
            search = search_path_from(out) if rc == 0 else []
            if not search:
                raise RuntimeError("`lake env printenv LEAN_PATH` printed no search path "
                                   f"(infrastructure; exit {rc}):\n{tail(out)}")

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
            rc, out, el = lean.compile(probe)
            st["packages"] = {"imports": sorted(set(pkg)), "exit": rc, "seconds": el,
                              "revisions": revs}
            verdict = classify_import_probe(pkg, rc, out, search_path=search)
            if verdict and verdict[0] == "reject":
                raise Reject("imports", verdict[1])
            if verdict:
                raise RuntimeError(verdict[1])

        # design (generated, trusted)
        dmod = os.path.join(stage, "Submission", "Design.lean")
        with open(dmod, "w") as fh:
            fh.write(design_module_text(task, env_path, latency))
        rc, out, el = lean.compile(dmod)
        st["design"] = {"exit": rc, "seconds": el}
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
            raise Reject("design", f"the design does not load (ls-sv refused it):\n{tail(out)}")
        free = UNSUPPORTED_FREE.search(out)
        if not free:
            raise RuntimeError("the design stage compiled, but its unsupported-construct check "
                               f"printed nothing (infrastructure):\n{tail(out)}")
        st["design"]["unsupported_free_points"] = int(free.group(1))

        if unproved:
            return finish_unproved(res, st, task, sv, env_path, do_score, ps_work, keep, oracle,
                                   lean if tactics else None, postsynth_mode, ppa_mode)

        # solution (timed)
        before = integrity_snapshot(stage, search)
        rc, out, el = lean.compile(sol, timeout=limit, bv_solver=allow_bv)
        st["solution"] = {"exit": rc, "seconds": el, "time_limit_s": limit,
                          "messages": tail(out, 6000)}
        if rc == 124:
            raise Reject("solution", f"the proof did not compile within {limit}s")
        if rc != 0:
            hint = bv_decide_hint(lean_text, out) if not allow_bv else None
            raise Reject("solution", f"the proof does not compile:\n{tail(out)}"
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
        rc, out, el = lean.run(cargs, timeout=vlimit)
        comp = comparator_report(out, goal_arg)
        st["comparator"] = {"exit": rc, "seconds": el, "result": comp}
        if rc == 124:
            raise Reject("comparator", f"the comparator did not finish within {vlimit}s")
        if comp is None:
            raise Reject("comparator", f"the comparator did not report:\n{tail(out)}")
        # the imports Lean itself recorded for the compiled solution, against the header the
        # allowlist read (WP-B review: the header reader and Lean must not disagree)
        problem = import_mismatch(imports, (comp.get("imports") or {}).get("Submission.Solution"))
        if problem:
            raise Reject("imports", problem)
        if not comp.get("accepted"):
            raise Reject("comparator", "; ".join(comp.get("errors", [])) or "rejected")

        # leanchecker (kernel replay of the submission's modules)
        rc, out, el = lean.run(["leanchecker", "Submission.Design", "Submission.Solution"],
                               timeout=vlimit)
        st["leanchecker"] = {"exit": rc, "seconds": el}
        if rc == 124:
            raise Reject("leanchecker", f"kernel replay did not finish within {vlimit}s")
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
            f"{block['unit_depth']} levels ({block['ppa_version']}; extra columns, not the board) "
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
                    f"{m['mapped_levels_sky130_v1']} levels ({m['ppa_mapped_version']}; extra columns, not the board) "
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


def score_clocked(res, st, task, sv, env_path, ps_work, mod, mode, top, sparams):
    """The clocked `score`, `postsynth` and `ppa` stages (PLAN4 Gate 2 steps 3 and 4; C7): the clocked
    flow (score/svgolf_seq.ys, ge_seq.json) at the scoring point; the clocked post-synthesis check
    (check/postsynth.py `run_clocked`) at each of the task's `postsynth.points` (the scoring point's
    netlist is the scored one, another point's is synthesized by the same flow); the sky130 columns
    of the scored netlist. RANKED: `area_um2` (sky130 A0', flops included) and `time_ps` = `cycles`
    x `period_ps`, the register-to-register period from the pinned liberty (clock-to-Q and setup
    included), `cycles` the declared latency n (1 for a seq-family task: one step per cycle). GE,
    unit depth and the flop count are extra columns."""
    ps_work["dir"] = work = tempfile.mkdtemp(prefix="svgolf-postsynth-")
    t0 = time.time()
    netlist = os.path.join(work, "netlist.v")
    sres = score.score([sv], top, sparams, netlist_out=netlist, flow="seq")
    sres["seconds"] = round(time.time() - t0, 2)
    st["score"] = sres
    points = [{n: int(v) for n, v in pt.items()} for pt in postsynth.config(task)["points"] or []]
    points = ([] if sparams in points else [sparams]) + points      # the scored netlist is always checked
    st["postsynth"] = {"points": []}
    try:
        for k, pt in enumerate(points):
            nl, pres = netlist, sres
            if pt != sparams:
                nl = os.path.join(work, f"netlist_{k}.v")
                pres = score.score([sv], top, pt, netlist_out=nl, flow="seq")
            pw = os.path.join(work, f"point_{k}")
            os.makedirs(pw)
            st["postsynth"]["points"].append(postsynth.run_clocked(
                task, env_path, nl, pres, pw, mod, pt, res.get("latency"), mode))
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
        res["errors"].append("--unproved: every check that needs no proof passed (source, "
                             "extract, banlist, fourstate, design"
                             + (", score, postsynth" if do_score else "")
                             + "); the proof stages were not run, so the design is not accepted")
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
    ap.add_argument("--time-limit", type=float, help="override the task's time limit (s)")
    ap.add_argument("--postsynth", choices=postsynth.MODES,
                    help="the post-synthesis mode: `light` (a deterministic subset of the vectors, "
                    "for local feedback) or `full` (the task's whole budget: competitions, "
                    "verification and the leaderboard run this). Default: $SVGOLF_POSTSYNTH, "
                    "else light")
    ap.add_argument("--ppa", choices=PPA_MODES, default="auto",
                    help="the extra sky130 PPA columns (score/ppa.py; the default board is "
                    "untouched): `auto` (default) weighs the scored netlist (flow A0') and maps "
                    "its canonical RTLIL with a real `abc -liberty` run (flow A1', the `mapped` "
                    "sub-object) when the pinned liberty is present and records `ppa: "
                    "{available: false, reason}` when it is not; `require` makes an absent "
                    "liberty an infrastructure error (official runs); `off` adds no key and no "
                    "stage")
    ap.add_argument("--latency", type=int,
                    help="with --unproved, for a tx-family or stream-family task: the latency n the goal pins at the "
                    "scoring point (a proved run reads it from the solution's `-- svgolf-latency:` line)")
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
        ap.error("give SOLUTION.lean, or --unproved without one")
    if args.tactics and not args.unproved:
        ap.error("--tactics is a pre-check for --unproved runs (before a proof exists)")
    for p in (args.task_dir, args.solution_sv) + ((args.solution_lean,) if args.solution_lean
                                                  else ()):
        if not os.path.exists(p):
            ap.error(f"no such file or directory: {p}")
    try:
        pmode = postsynth.resolve_mode(args.postsynth)
    except postsynth.InfraError as e:
        ap.error(str(e))
    wrap = args.lean_wrap.split()
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
                    args.tactics, pmode, args.ppa, args.latency)
    except RuntimeError as e:
        print(json.dumps({"accepted": False, "stage": "infrastructure", "errors": [str(e)]},
                         indent=2))
        return 2
    finally:
        if not args.keep and not args.stage_dir:
            shutil.rmtree(stage, ignore_errors=True)
        sandbox.policy().close()
    if args.keep or args.stage_dir:
        res.update(dev_hint(stage, wrap, args.unproved, res))
    if args.unproved:
        for w in res.get("warnings", []):
            log(w)     # the same advisory line as in the JSON's `warnings`
    text = json.dumps(res, indent=2, sort_keys=True)
    print(text)
    if args.json:
        with open(args.json, "w") as fh:
            fh.write(text + "\n")
    return 0 if res["accepted"] else 1


if __name__ == "__main__":
    sys.exit(main())
