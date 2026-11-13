#!/usr/bin/env python3.12
"""svGolf's regression runner: everything, from one entry point.

    python3.12 tests/run.py [--only TASK,...] [--skip STEP,...] [--full]
                            [--update-scores] [--keep-going]

Exit status 0 iff every check below passes; a compact summary table is
printed at the end.

POST-SYNTHESIS MODES (WP-C2): the postsynth check has a `light` mode (a
deterministic subset of the vectors; check.py's default, for local feedback)
and a `full` one (the task's whole budget). This runner pins the verdicts in
FULL mode everywhere it runs check.py or check/postsynth.py (`--postsynth
full` / `mode="full"`, explicitly: the environment is never trusted), except
for the attacks of tests/expected.json: an entry's `postsynth_mode` (`light`
when absent, `full` for an attack that ONLY the full check rejects) is the
mode of its `postsynth_alone` run and of its check.py run. The `modes` step
tests the selection itself.

STEPS, in order:

  layout      the repository layout: each task.json against the schema
              (README.md, "A task directory"); every reference a proved pair
              `<stem>.sv` + `<stem>.lean` (a draft task: no reference, its
              goalpost `<stem>.sv` + `<stem>.partial.lean`; a STATEMENT draft,
              `statement_draft`: the goalpost alone, no partial proof yet, and
              for a latency kind the goalpost's `latency`); nothing else in
              `tasks/<name>/reference/`; no extractor output (`*.sv.json`,
              `*.probes.json`) outside `.lake/`; `tests/expected.json` lists
              exactly the designs on disk, and every baseline it lists has a
              proof file (`lean`, which the step `baseline-proofs` checks);
              the aggregators `tasks.lean` and
              `tests.lean` import every Spec and every Refute (but the
              PENDING_REFUTES, which `tests.lean` must not import); every
              PENDING_STAGES row is a negative of `tests/expected.json` at
              another stage than the pinned one;
              the generators' `--check` (`tests/mul/unproved/gen_dadda.py`,
              `tests/clmul/unproved/gen_clmul.py`, the two proof generators of
              `tests/aes_sbox/validate/`); every task's `time_limit_s`
              is the one limit, every reference a task.json lists has cold runs in CPU
              seconds in `score/time_limits.json` and none is over the limit
              (`score/time_limits.py --check`, which also names every reference over the
              150 CPU s target without failing)
  build       `lake build` of the svGolf project (SvGolf, tasks, tests):
              every statement, and every kernel-checked refutation of a
              negative design (`tests/<name>/negative/Refute.lean`, whose
              designs `load_sv` extracts at elaboration time), but the
              PENDING_REFUTES (the `negatives` step builds those)
  unit        score/test_score.py, score/test_srcgate.py,
              score/banlist.py --selftest, score/fourstate.py --selftest,
              score/time_limits.py --selftest,
              tests/imports/test_allowlist.py (the import allowlist and the
              import closure of the sv_comb tactic library),
              tests/fdivp/shared_sections.py (and --selftest: the sections
              the Newton reference of `fdivp` copies from D3 are unchanged),
              tests/checker/test_advisories.py (no Lean: check.py's
              `dev_hint` and elapsed-time line, the `--tactics` probe and its
              output classifier, the functional smoke check on synthetic ls-sv
              rows, every task's `oracle.py` against independent Python
              arithmetic, the post-synthesis mode selection and `light_select`,
              and the generated `Submission.Design` of the unsupported-construct
              check),
              tests/checker/test_design_stage.py (no Lean: the `design` stage
              rejecting an unsupported construct, on check.py's real early
              stages with a fake Lean),
              tests/checker/test_lift_banlist.py (no Lean: `check.py
              --lift-banlist` takes a banned design past the banlist to the
              proof stages, the plain banlist still rejects it, and a lifted
              result is never accepted and never a record),
              tests/checker/test_import_packages.py (no Lean: imports from the
              Mathlib packages, WP-B: the import probe, its rejection /
              infrastructure-error split, the package-olean tripwire),
              tests/checker/test_layout.py (check/layout.py: svGolf inside
              lean-surfaces and standalone, on synthetic trees, and the site
              generator's two roots),
              tests/checker/test_slang_errors.py (no Lean, WP-RB1: a program slang
              reports illegal is rejected at `fourstate` for a task with an EMPTY
              banlist, under its own header, and at `banlist` otherwise),
              tests/checker/test_clocked.py (no Lean, PLAN4 Gate 2: the clocked
              source-gate rules on tests/seq_counter/attacks/, the latency header,
              the generated goals of seq-family, tx-family, stream-family and
              react-family),
              tests/checker/test_clocked_post.py (no Lean: the clocked score,
              post-synthesis check and negatives, tests/seq_tx/, the sorter's
              stream mutants and the arbiter's reactive check: the goalpost passes,
              a Mealy output, an unreset grant and fixed priority each fail on
              their own clause),
              tests/checker/test_postsynth_unknown.py (Yosys: an unknown-valued
              constant in the netlist is refused where Yosys's own reader shows
              something reading it, and accepted where nothing does),
              tests/checker/test_postsynth_loops.py (Yosys and Verilator: a
              combinational loop in the netlist is refused bit by bit, and the
              bit aliases of merged flip-flops, which Verilator's UNOPTFLAT
              called a loop, pass and simulate),
              score/test_ppa.py (the sky130 PPA columns, stage 1),
              score/test_ppa_opensta.py (ppa.py's STA against OpenSTA's recorded
              arrivals, cell arcs to clocked periods, the input-drive convention),
              score/test_ppa_asap7.py (the asap7 alternative library of
              `ppa.py --pdk asap7`; its real-library tests skip without the files),
              tests/checker/test_ppa_wiring.py (no Lean, fake Lean: check.py's
              `--ppa off|auto|require` and the absent-liberty path; `off` equals,
              character for character, the baseline checker's result on the `add`
              and `aes_sbox` references and `auto` that plus exactly the key `ppa` and
              the stage `stages.ppa` (goldens recorded from the commit before the
              wiring, tests/checker/ppa_wiring/); the integrity tripwire names
              score/ppa.py, score/ppa_pins.json and flow A1''s score/ppa_mapped.ys and
              score/ppa_mapped_pins.json; the `ppa.mapped` sub-object and its failure
              modes), and tests/site/ (the site generator, site/build.py: one
              offline build into a temporary directory, its links, its verbatim
              sources and downloads, its frontier against the leaderboard's, a
              second byte-identical build, the denylist; the highlighter, the
              Markdown renderer and the chart scales)
  leaderboard leaderboard/leaderboard.py: tests/leaderboard/test_leaderboard.py
              (synthetic check results, no Lean, no Yosys: record round trip and
              tamper detection, refusal of rejected submissions, the Pareto
              frontier, the depth budget, the Markdown golden file, the CLI end
              to end) and `leaderboard.py verify --offline` on the committed
              records (hashes, stored files, score arithmetic);
              tests/leaderboard/test_sizes.py and `leaderboard.py sizes` (the
              designs at other sizes: planted faults, then the committed files)
  modes       the post-synthesis modes (no Lean): `_example` and `mul_n` through
              check/postsynth.py in both modes: the record says which ran, the light
              vector counts stay within the task's `light_vectors` and under the full
              set's, both modes share the seed and the full set's size, the full
              record carries today's counts (`vectors == full_vectors`), and
              the command line / $SVGOLF_POSTSYNTH select the mode as documented
  comparator  tests/checker/test_comparator.py (REAL Lean, a hand-built module chain, no
              Mathlib, no staging tree): the honest chain accepted, a "package" whose
              `False` was added with the kernel check off (it passes the comparator's
              kernel check and axiom walk, and is rejected by the replay of the
              dependency closure), a package axiom, a toolchain module resolved from a
              directory ahead of the toolchain's, an `extern` under the submission
              prefix (WP-B review round); and tests/checker/test_bv_decide.py (WP-BV:
              the DORMANT re-verification of bv_decide axioms: real proofs accepted when the
              comparator is given --bv-decide, forged and malformed axioms, a hostile shared or
              deep term, ofReduceBool and native_decide rejected, and every bv_decide axiom
              rejected, naming the policy, without the flag, which is what check.py passes); and
              tests/checker/test_xsafe_twin.py (REAL Lean: rule 3's Python twin, check/clocked_rules.py,
              against `xsafeB` of the designs `load_sv` loads from tests/seq_counter/xsafe/, at every
              probe point: sound, and in agreement where no earlier stage refuses)
  canon       the canonical scoring flow (score/canon.ys, then score/svgolf.ys
              in a fresh Yosys process): every reference and draft goalpost,
              re-laid-out (blank lines, line joins, one token per line,
              re-indentation, tabs, comma breaks) and with its internal
              signals, labels and genvars renamed, has a BYTE-IDENTICAL
              canonical RTLIL and the same score; with its module items
              reordered, the same score; with the operands of its commutative
              operators swapped, the score tests/expected.json records
              (`canonical_layout`: expression structure is scored, it is not
              normalized). tests/canon/variants.py makes the variants
  references  every proved reference through check.py: ACCEPTED (so it passes
              the postsynth stage), and its score at the scoring point equal
              to tests/expected.json; its other expected points through
              score.py (not for a reference marked `same_design_as`: a
              byte-identical copy of another one, e.g. `add_n_byhand`, whose
              .sv the layout step compares and whose validation is its twin's);
              for a task with an `oracle`, the advisory functional check agrees
              on every vector of the postsynth stage (a proved design computes
              the task's function: a mismatch would be an oracle bug). A CLOCKED
              task (tx-family, seq-family, stream-family, react-family): the clocked postsynth record at the
              scoring point and every `postsynth.points` point (full mode, every
              seed, no failure; its oracle check is binding there), the ranked
              score (um^2, cycles x period, flops) beside GE and depth, the
              clocked ppa block; no score.py points (its flow is the comb one)
  drafts      a draft task's goalpost through check.py with its partial Lean
              file: rejected exactly at the expected stage (every stage before
              it passes); its scores; the postsynth check at the scoring point.
              A statement draft: `check.py --unproved` (`--latency`: its
              goalpost's) reaches `unproved`, and for a clocked kind its clocked
              postsynth record passes as a reference's and its ranked score is
              tests/expected.json's (when it records one); a draft of a kind
              check.py has no checker for (`checker_kind`) is skipped
  negatives   every negative design through check.py with the task's first
              reference proof (a draft task: its partial file; a statement
              draft: skipped): rejected at its expected stage; its expected
              scores, if any; but a PENDING_STAGES row (the three
              `only_n16.sv`, until the int32 port round) must be rejected at
              its pinned stage, `design`, with the loader's refusal. And each
              PENDING_REFUTES module, built alone
              (`lake build tests.<name>.negative.Refute`): it must fail with
              its pinned message; one that builds fails the step until
              `tests.lean` imports it again and the entry is dropped
  baselines   every baseline (a PROVED comparison design, never an entry,
              decided 2026-11-12; `banned`: one with an operator the task bans)
              scored at its expected points (score.py, which applies no
              banlist: "the banlist lifted"); the banlist's verdict as
              expected.json says (`banned`); `same_tokens_as` checked; the
              4-state rules (score/fourstate.py, check.py's `fourstate` stage)
              pass at every scored point; the
              postsynth check (check/postsynth.py) at its `postsynth_points`
              (default: every scored point): ls-sv and the scored netlist
              agree, so no legitimate design is falsely rejected
  baseline-proofs
              every baseline WITH ITS PROOF (tests/expected.json `lean`) through
              check.py: an unbanned one must be ACCEPTED, a banned one (the
              task's banlist rejects it) is checked with `--lift-banlist` and
              must end at the pseudo-stage `lifted` (`lifted_ok`: every stage
              passed, the proof's included; never an entry) with the task
              banlist's own verdict `rejects`; in both cases the comparator's
              axioms within the task's allowed set (propext, Classical.choice,
              Quot.sound), the full post-synthesis check, and the score at the
              scoring point equal to tests/expected.json's. A baseline without
              a proof fails the step (the site shows no design without one)
  ppa         the sky130 PPA columns (WP-X3; EXTRA columns, the default board is
              untouched) of every design of score/tests/ppa/designs.json that the
              `references` step did not already see in a real check.py result: the
              pinned flow's scored netlist, weighed by check.py's own `ppa_block`,
              equal to the goldens of score/tests/ppa/expected_ppa.json; and the
              eight NETLIST IDIOMS of score/tests/ppa/idioms.json (run-time bit
              select, variable shift, case mux, constant table, ...: designs whose
              netlists carry the dead public-named wires of techmapped cells), equal
              to expected_idioms.json, whatever `--only` says. The goldens pin
              (GE, depth, gates) and (um^2, ps, levels, cells, netlist hash); every
              weighed block is also checked for the columns they do not pin
              (`ppa_block_problems`: area = 1e-4 um^2 / 10^4, the cell histogram
              against the cell count and, through the live liberty, the area; setup,
              liberty file and the shape of `critical` against the pins). The
              `references` step checks the same on the `ppa` block of each
              reference's real check.py result (run with `--ppa require`), and that
              the rest of the result is, character for character, the baseline
              checker's (tests/checker/ppa_wiring/*_full.baseline.json: the `add` and
              `aes_sbox` references). WP-X4: the same designs through flow A1' (the
              real `abc -liberty` mapping, the `ppa.mapped` sub-object, one more Yosys
              run per design), equal to the goldens of
              score/tests/ppa/expected_ppa_mapped.json (canonical RTLIL hash, um^2,
              ps, cells, cell levels, buffers, inverters, constants, mapped netlist
              hash), under the recorded script, liberty, Yosys and ABC builds, and
              checked for internal consistency (`ppa_mapped_block_problems`) in the
              `references` and the `ppa` steps alike. THE PINNED LIBERTY (12.8 MB, not in the
              repository: `python3.12 score/ppa.py --fetch-liberty`): where it is
              present the suite sets SVGOLF_PPA_REQUIRE_LIB=1 (the real-library tests
              of score/test_ppa.py cannot skip silently) and runs the references with
              `--ppa require`; where it is absent the PPA checks above are SKIPPED
              with a message (recorded as ok, saying SKIPPED) and the references run
              `--ppa auto`: nothing unrelated fails.
  validate    simulation (Verilator, ls-sv `run2`, post-synthesis
              netlists): the quick plans below by default, the documented
              full plans with --full (see VALIDATION and its timings)
  attacks     the checker's own defenses, on `_example`: submissions this
              script writes to a temporary directory (they are test inputs,
              never part of any build) must be rejected at their stage; and
              the designs of `tests/<task>/attacks/` (ls-sv/Yosys
              disagreements: x/z case items and `==` operands, x from a
              constant division by zero, an out-of-range read, an undriven
              net, `===` against x, `unique`/`priority` violations, a for loop
              writing its counter, `.sum()`), each through `check.py
              --unproved` (they have no proof; an entry with `lean` is
              submitted with a reference proof instead: `reference` the
              task's first, `reference/<stem>.lean` that one, as the
              attacks of fdivp's three proofs), rejected at the stage
              tests/expected.json gives (`source`, `fourstate`, `banlist`;
              `design` for a design that loads with an Unsupported node: the
              functions and latches ls-sv cannot run, WP-C3, whose entry may
              add `message_contains`, a phrase the rejection must carry, or a
              list of phrases of which it must carry one: `why` says why),
              and, where it says `postsynth_alone`, through the postsynth
              check with the source gate and the fourstate stage bypassed:
              what that sampling check would do on its own (`rejects`, or
              `passes` where the difference is confined to a region its
              vectors do not reach, which is why the static refusals exist).
              `postsynth_mode` (`light`, or `full` for an attack that only the
              full check rejects) is the mode of that run and of the check.py run.
              An entry may also carry the ADVISORY checks' expectations
              (neither changes the stage): `args` (extra check.py flags, e.g.
              `--tactics`), `functional` (`warns`: the task's oracle finds
              mismatches and the result has ONE `warnings` line, as for the
              wrong adder `tests/add/attacks/wrong_carry.sv`; `agrees`: it
              finds none) and `tactics` (`in_fragment` and a message the
              tactic's refusal must contain)

Scores are compared exactly: area in milli-GE, depth, gate count and the gate
mix; tests/expected.json's `flow` (the Yosys version and the sha256 of
score/canon.ys, score/svgolf.ys and score/ge.json) must match the pinned flow.
`--update-scores` rewrites tests/expected.json with the measured values
instead, `flow` included (after a deliberate change of the pinned flow;
review the diff).

Runtime (measured 2026-10-28, 188 checks, one Lean job at a time): about 25
minutes of work when the Lean slot is free: the build 45 to 90 s when the
Refute modules re-elaborate, canon 70 s, ~60 check.py runs (references,
drafts, negatives, attacks) of 10 to 60 s each (the mul reference about 90 s
with its postsynth stage), baselines 6 min (postsynth of the 16-bit Dadda
trees, then baselines: 83 and 162 s; since 2026-11-12 the parametric Dadda
baseline's full postsynth alone takes 800 to 900 s of the 900 s cap),
validate 2.5 min quick; waiting for the slot comes on top. baseline-proofs
(measured 2026-11-12, an Apple M2 Pro under other jobs' load, the eleven
baselines' full checks one after another): about 43 minutes, the longest
dadda_rc (1245 s, nearly all of it its full postsynth; its solution stage 47
CPU s of the 300), then fdivp_d2 (339 s; solution 188 CPU s). --full adds hours (fdivp's full validation plan, the mul
reference's full plan, add's full `validate.py` and `verilator.py`, postsynth
of every baseline at every scored point).

Every Lean invocation (lake build, and check.py's) goes through
$SVGOLF_LEAN_WRAP (e.g. a slot-limiting wrapper). Run it WITHOUT that wrapper
around it: the script calls the wrapper itself.
"""

import argparse
import difflib
import filecmp
import glob
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
CHECK = os.path.join(SVGOLF, "check.py")
# check.py with the DORMANT bv_decide support forced on, for the groundwork rows only (WP-BV G3): a wrapper script that loads
# check.py and sets its constant inside its own process. check.py itself reads no switch for it.
CHECK_BV = os.path.join(SVGOLF, "tests", "checker", "check_bv_enabled.py")
EXPECTED = os.path.join(HERE, "expected.json")
sys.path.insert(0, os.path.join(SVGOLF, "score"))
sys.path.insert(0, os.path.join(SVGOLF, "check"))
sys.path.insert(0, os.path.join(HERE, "checker"))
import banlist  # noqa: E402
import byte_identity  # noqa: E402  (tests/checker/byte_identity.py: the baseline goldens of the --ppa wiring)
import envelope  # noqa: E402
import fourstate  # noqa: E402
import postsynth  # noqa: E402
import ppa  # noqa: E402
import score  # noqa: E402

PY = sys.executable
_CHECKPY = []


def checkpy():
    """check.py as a module (its `unsupported_check_points` says how many points the design
    stage must have tested), loaded once."""
    if not _CHECKPY:
        import importlib.util
        spec = importlib.util.spec_from_file_location("svgolf_check_py_runner", CHECK)
        mod = importlib.util.module_from_spec(spec)
        sys.modules["svgolf_check_py_runner"] = mod
        spec.loader.exec_module(mod)
        _CHECKPY.append(mod)
    return _CHECKPY[0]


STEPS = ["layout", "build", "unit", "comparator", "leaderboard", "modes", "canon", "references",
         "drafts", "negatives", "baselines", "baseline-proofs", "ppa", "validate", "attacks", "sandbox"]

# The refutations that wait for the int32 port round: the pinned ls-sv's loader refuses each one's
# `only_n16.sv` (`PDesign.int32Agrees`: at the defaults an INT-class constant expression leaves the 32-bit
# range), so the module does not build at the pin. `tests.lean` does not import them, which keeps the default
# `lake build` green; they are kept unchanged, and the `negatives` step builds each one alone and pins its
# known failure: module -> the phrases its error output must carry. A module that builds fails that step: import
# it in `tests.lean` again and drop it here.
PENDING_REFUTES = {
    f"tests.{t}.negative.Refute": (f"tests/{t}/negative/Refute.lean", f"tests/{t}/negative/only_n16.sv",
                                   "REFUSED", "INT-class constant expression leaves the 32-bit range",
                                   "(`PDesign.int32Agrees`)")
    for t in ("add", "mul", "clmul")
}
# The check.py rows of the same designs wait for the same round: check.py loads each `only_n16.sv` at its `design`
# stage, where the pinned loader refuses it, so the run never reaches the `solution` stage that tests/expected.json
# gives it (the proof's failure, which the refutation above shows). Until the int32 port round the `negatives`
# step pins the design-stage refusal instead: "<task>/<stem>" -> (the stage check.py stops at now, the start of its
# first error, the phrases that error's first Lean error line must carry). tests/expected.json keeps the stage the
# row has after that round, and its scores are checked as before. A row that check.py rejects any other way fails
# the step (one rejected at its expected.json stage: drop it here, with its PENDING_REFUTES entry).
PENDING_STAGES = {
    f"{t}/only_n16": ("design", "the design does not load (ls-sv refused it)", "REFUSED",
                      "INT-class constant expression leaves the 32-bit range", "(`PDesign.int32Agrees`)")
    for t in ("add", "mul", "clmul")
}
WRAP = os.environ.get("SVGOLF_LEAN_WRAP", "").split()

# The sky130 PPA columns (WP-X3). "present": the pinned liberty opens (sha256 verified); "absent": there is no file
# (the PPA checks are skipped with a message); "invalid": there is a file that is not the pinned one (one loud failure).
PPA_STATE = {"state": None, "path": None, "why": ""}
PPA_REFERENCE_NAMES = set()      # designs.json names whose `ppa` block the references step has already checked
PPA_NOTED = []                   # the one "skipped" message of the references step


def ppa_state():
    """Look at the pinned liberty once: ("present" | "absent" | "invalid", path, reason)."""
    if PPA_STATE["state"] is None:
        path = ppa.find_liberty()
        PPA_STATE["path"] = path
        if not os.path.isfile(path):
            PPA_STATE.update(state="absent", why=f"no file at {path}")
        else:
            try:
                ppa.open_library()
                PPA_STATE.update(state="present", why="")
            except (ppa.PpaError, OSError) as e:
                PPA_STATE.update(state="invalid", why=" ".join(str(e).split()))
    return PPA_STATE["state"], PPA_STATE["path"], PPA_STATE["why"]


def ppa_mode():
    """The `--ppa` mode of the suite's official-artifact runs: `require` where the pinned liberty is present (the
    leaderboard's mode), else `auto` (the PPA checks are skipped, nothing else changes)."""
    return "require" if ppa_state()[0] == "present" else "auto"


def ppa_skip_note():
    return (f"SKIPPED: the pinned sky130 liberty is {ppa_state()[0]} ({ppa_state()[2]}); fetch it with "
            "`python3.12 score/ppa.py --fetch-liberty` (or point $SVGOLF_SKY130_LIB at a copy) to run the PPA checks")

# ---------------------------------------------------------------------------
# results
# ---------------------------------------------------------------------------

RESULTS = []   # (step, item, ok, detail, seconds)


def record(step, item, ok, detail="", seconds=None):
    RESULTS.append((step, item, ok, detail, seconds))
    t = f" [{seconds:.0f}s]" if seconds is not None and seconds >= 1 else ""
    print(f"[{'ok' if ok else 'FAIL'}] {step}: {item}: {detail}{t}", flush=True)
    return ok


def rel(path):
    return os.path.relpath(path, SVGOLF)


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def load_json(path):
    with open(path) as fh:
        return json.load(fh)


def tasks_on_disk():
    d = os.path.join(SVGOLF, "tasks")
    return sorted(t for t in os.listdir(d) if os.path.isfile(os.path.join(d, t, "task.json")))


def task_json(t):
    return load_json(os.path.join(SVGOLF, "tasks", t, "task.json"))


def checker_kind(task):
    """Whether check.py has a checker for the task's `kind` (its `KINDS`); the drafts and negatives steps skip
    a draft of a kind it does not know, saying so."""
    return task.get("kind") in checkpy().KINDS


def statement_draft(t, task):
    """A DRAFT task whose partial proof file does not exist yet (the sorter, PLAN4 Gate 5): its goalpost .sv
    must exist, and for a `LATENCY_KINDS` task its `draft_reference.latency` (the goalpost's n at the scoring
    point); the drafts step checks the goalpost with `check.py --unproved`, the negatives step skips it."""
    lean = (task.get("draft_reference") or {}).get("lean", "")
    return task.get("status") == "draft" and not os.path.isfile(os.path.join(SVGOLF, "tasks", t, lean))


def first_lean(t, task):
    """The Lean file negatives are submitted with: the first reference's
    proof, or a draft's partial file."""
    if task.get("status") == "draft":
        return os.path.join(SVGOLF, "tasks", t, task["draft_reference"]["lean"])
    return os.path.join(SVGOLF, "tasks", t, task["references"][0]["lean"])


def design_path(t, kind, stem, entry):
    if kind == "references":
        return os.path.join(SVGOLF, "tasks", t, "reference", stem + ".sv")
    sub = {"negatives": "negative", "baselines": "baselines", "attacks": "attacks"}[kind]
    return os.path.join(SVGOLF, "tests", t, entry.get("sv") or os.path.join(sub, stem + ".sv"))


def parse_point(p):
    return {} if p == "default" else envelope.parse_point(p)


def bv_enabled_task_dir(tmp):
    """A copy of tasks/_example whose task.json says `allow_bv_decide: true`: the groundwork rows run
    check_bv_enabled.py (the dormant support forced on) on it; the shipped tasks say false."""
    d = os.path.join(tmp, "task_bv_enabled")
    if not os.path.isdir(d):
        shutil.copytree(os.path.join(SVGOLF, "tasks", "_example"), d)
        with open(os.path.join(d, "task.json")) as fh:
            t = json.load(fh)
        t["allow_bv_decide"] = True
        with open(os.path.join(d, "task.json"), "w") as fh:
            json.dump(t, fh, indent=2)
    return d


def run_check(task_dir, sv, lean, extra=(), postsynth_mode="full", ppa_flag="off", env=None, script=None):
    """check.py on one submission (`lean` None: with `--unproved` in `extra`). The
    post-synthesis mode is passed EXPLICITLY (`--postsynth`): this runner pins verdicts in
    full mode and never depends on $SVGOLF_POSTSYNTH or on check.py's default. The same for
    `--ppa`: `off` for the runs that are not official artifacts (they stop before the PPA
    stage or have no use for it), the references pass `ppa_mode()`."""
    t0 = time.time()
    proc = subprocess.run([PY, script or CHECK, task_dir, sv] + ([lean] if lean else []) + list(extra)
                          + ["--postsynth", postsynth_mode, "--ppa", ppa_flag],
                          capture_output=True, text=True, env=env)
    try:
        res = json.loads(proc.stdout)
    except json.JSONDecodeError:
        res = {"accepted": False, "stage": "crash",
               "errors": [proc.stdout[-2000:] + proc.stderr[-2000:]]}
    res["_seconds"] = time.time() - t0
    res["_exit"] = proc.returncode
    return res


def verdict(res):
    if res.get("accepted"):
        return "accepted"
    if res.get("unproved_ok"):
        return "unproved (every check without a proof passed)"
    return f"rejected at {res.get('stage')}"


def clean_unproved(res):
    """check.py's contract for a clean `--unproved` run: stage `unproved`, not accepted, `unproved_ok`, no
    `errors` (the sentence is in `notes`) and exit status 0."""
    return (res.get("stage") == "unproved" and not res.get("accepted") and res.get("unproved_ok") is True
            and not res.get("errors") and bool(res.get("notes")) and res.get("_exit") == 0)


def first_error(res):
    """The rejection's headline, and its first Lean/tool error line if any (a clean `--unproved` run: its note)."""
    errs = res.get("errors") or res.get("notes") or ["?"]
    lines = (errs[0] or "?").splitlines() or ["?"]
    # (check.py's `errors_first` heads a long Lean output with "the errors (n, ...):", then the error lines)
    detail = next((ln.strip() for ln in lines[1:] if "error" in ln and not ln.startswith("the errors (")), "")
    return (lines[0] + (" " + detail if detail else ""))[:220]


SCORE_KEYS = ("area_mge", "depth", "num_gates", "gates")
# a clocked task's ranked score (C7: sky130 um^2, and cycles x the register-to-register period) and its flop count
CLOCKED_SCORE_KEYS = ("area_um2", "period_ps", "cycles", "time_ps", "ffs")


def same_score(got, want):
    return all(got.get(k) == want.get(k) for k in SCORE_KEYS + tuple(k for k in CLOCKED_SCORE_KEYS if k in want))


def show_score(s):
    return f"{s['area_ge']} GE, depth {s['depth']}" + (
        f"; {s['area_um2']} um^2, {s['cycles']} x {s['period_ps']} = {s['time_ps']} ps, {s['ffs']} flops"
        if "time_ps" in s else "")


def score_diff(got, want):
    """The SCORE_KEYS that differ, with the gate-mix difference."""
    out = []
    for k in ("area_mge", "depth", "num_gates"):
        if got.get(k) != want.get(k):
            out.append(f"{k} {got.get(k)} (expected {want.get(k)})")
    g, w = got.get("gates") or {}, want.get("gates") or {}
    mix = {t: f"{w.get(t, 0)}->{g.get(t, 0)}" for t in sorted(set(g) | set(w))
           if g.get(t, 0) != w.get(t, 0)}
    if mix:
        out.append(f"gates {mix}")
    return "; ".join(out)


def current_flow(flow="comb"):
    """The pin of score.py's flow `flow` as it is now: "comb" (svgolf.ys, ge.json; tests/expected.json `flow`) or
    "seq" (svgolf_seq.ys, ge_seq.json; `flow_seq`, the pin a clocked task's records are compared with)."""
    script, table = score.FLOWS[flow]
    return {"yosys_version": score.yosys_version(score.yosys_bin()),
            "canon_script_sha256": score.sha256_file(score.CANON_SCRIPT),
            "script_sha256": score.sha256_file(script),
            "ge_table_sha256": score.sha256_file(table)}


def measure(sv, top, point):
    try:
        r = score.score([sv], top, parse_point(point))
    except score.ScoreError as e:
        return None, str(e).splitlines()[0][:200]
    return {"area_ge": r["area_ge"], "area_mge": r["area_mge"], "depth": r["depth"],
            "num_gates": r["num_gates"], "gates": r["gates"]}, None


def check_scores(step, label, sv, top, scores, args, skip=()):
    """Score `sv` at every expected point (except `skip`) and compare."""
    good = True
    for point, want in scores.items():
        if point in skip:
            continue
        t0 = time.time()
        got, err = measure(sv, top, point)
        if got is None:
            good &= record(step, f"{label} score {point}", False, err, time.time() - t0)
            continue
        if args.update_scores:
            scores[point] = got
            record(step, f"{label} score {point}", True, f"recorded {show_score(got)}")
            continue
        ok = same_score(got, want)
        good &= record(step, f"{label} score {point}", ok,
                       f"{show_score(got)}" + ("" if ok else f": {score_diff(got, want)}"),
                       time.time() - t0)
    return good


# ---------------------------------------------------------------------------
# layout
# ---------------------------------------------------------------------------

TASK_KEYS = {"name", "title", "status", "kind", "top", "parameters", "ports", "statement",
             "banlist", "probe_points", "scoring", "backstop_points", "allowed_axioms",
             "allow_bv_decide", "time_limit_s", "verify_time_limit_s", "references",
             "draft_reference", "postsynth", "leaderboard", "oracle",
             "clock", "reset", "protocol",     # the clocked kinds (PLAN4 Gate 2)
             "input_drive"}                    # the cell driving the primary inputs (sky130_a0_v3; default buf_8)


def _dev_only():
    """The test for a development-only path (relative to svgolf/): one the public export leaves out
    (tools/export_public.py's drop list). The export leaves itself out too, so in a public tree
    nothing is development-only."""
    path = os.path.join(SVGOLF, "tools", "export_public.py")
    if not os.path.isfile(path):
        return lambda rel: False
    spec = importlib.util.spec_from_file_location("svgolf_export_public", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return lambda rel: mod.dropped(rel) is not None


dev_only = _dev_only()


def step_layout(tasks, expected):
    good = True
    for t in tasks:
        task = task_json(t)
        tdir = os.path.join(SVGOLF, "tasks", t)
        errs = []
        unknown = sorted(k for k in task if k not in TASK_KEYS and not k.startswith("_"))
        if unknown:
            errs.append(f"unknown keys {unknown} (README.md documents the schema)")
        if task.get("name") != t:
            errs.append(f"name {task.get('name')!r} is not the directory name")
        # every task bans run-time / % ** (banlist.py ALWAYS_BANNED, since 2026-11-06): task_banlist adds them anyway,
        # and the task.json lists them so that every reader of the file (the site, the READMEs) sees the rule
        missing_ops = [op for op in banlist.ALWAYS_BANNED if op not in task.get("banlist", {}).get("operators", [])]
        if missing_ops:
            errs.append(f"banlist.operators lacks {missing_ops}: every task bans run-time / % ** (README.md, Rules)")
        try:
            postsynth.config(task)
        except postsynth.InfraError as e:
            errs.append(str(e))
        drive = None
        try:
            # sky130_a0_v3: `input_drive`, if present, is one of the pins' allowed cells (absent: the pins' default)
            drive = ppa.input_drive_of(task, ppa.Pins())
        except ppa.PpaError as e:
            errs.append(str(e))
        if task.get("oracle") or os.path.exists(os.path.join(tdir, "oracle.py")):
            # the advisory functional oracle (README.md, task.json `oracle`): named in task.json
            # (and so on disk), and it loads
            if task.get("oracle") != "oracle.py":
                errs.append(f"oracle {task.get('oracle')!r}: task.json must name `oracle.py` (the "
                            "file of the task directory)")
            else:
                fn, why = postsynth.load_oracle(tdir, task)
                if fn is None:
                    errs.append(why)
        status = task.get("status")
        # no proof library per task (decided 2026-11-03): reusable proof code goes to LeanModels/Sv/Lib, the
        # rest into the task's reference proof. REVIEW.md is the review of the statement; a development-only
        # file (one the public export leaves out: `dev_only`) is allowed too. Properties.lean names the parts
        # of the statement and proves the statement equivalent to them (not a proof library: nothing about
        # designs); properties.json is their plain-words text for the site
        allowed = {"task.json", "Spec.lean", "README.md", "REVIEW.md", "reference", "oracle.py",
                   "Properties.lean", "properties.json"}
        allowed |= {f for f in os.listdir(tdir) if dev_only(f"tasks/{t}/{f}")}
        if t == "fdivp":
            # the trusted IEEE 754 spec beside the statement, and its (untrusted) validation tooling
            allowed |= {"IEEE754.lean", "spec_validate"}
        extra = sorted(set(os.listdir(tdir)) - allowed)
        if extra:
            errs.append(f"files a player does not need in tasks/{t}/: {extra} (tests go to tests/{t}/)")
        files = []
        if status == "ready":
            refs = task.get("references") or []
            if not refs:
                errs.append("a ready task needs at least one proved reference")
            if "draft_reference" in task:
                errs.append("a ready task has no draft_reference")
            for r in refs:
                sv, lean = r.get("sv", ""), r.get("lean", "")
                if not (sv.startswith("reference/") and sv.endswith(".sv")
                        and lean == sv[:-3] + ".lean"):
                    errs.append(f"reference {r} is not a pair reference/<stem>.sv + <stem>.lean")
                files += [sv, lean]
        elif status == "draft":
            if task.get("references"):
                errs.append("a draft task lists no (proved) references")
            d = task.get("draft_reference") or {}
            sv, lean = d.get("sv", ""), d.get("lean", "")
            if not (sv.startswith("reference/") and lean == sv[:-3] + ".partial.lean"):
                errs.append(f"draft_reference {d} is not reference/<stem>.sv + <stem>.partial.lean")
            files += [sv, lean]
            if statement_draft(t, task):
                files.remove(lean)      # a statement draft: no partial proof yet
                lat = d.get("latency")
                if task.get("kind") in checkpy().LATENCY_KINDS and not (type(lat) is int and lat >= 1):
                    errs.append(f"draft_reference.latency {lat!r}: a statement draft of a {task.get('kind')} "
                                "task names its goalpost's latency at the scoring point (an integer >= 1)")
        else:
            errs.append(f"status {status!r} is neither `ready` nor `draft`")
        for f in files:
            if not os.path.isfile(os.path.join(tdir, f)):
                errs.append(f"missing {f}")
        on_disk = sorted(os.listdir(os.path.join(tdir, "reference")))
        listed = {os.path.basename(f) for f in files}
        # reference/LICENSES/: the licence texts that the provenance headers of the listed designs name as
        # `LICENSES/<file>` (third-party code under a licence that asks for its text to ship with it, e.g.
        # fdivp_srt.sv's Apache-2.0 WITH SHL-2.1 part): every file there is named, every named file is there
        lic = os.path.join(tdir, "reference", "LICENSES")
        if os.path.isdir(lic):
            named = set()
            for f in files:
                if f.endswith(".sv") and os.path.isfile(os.path.join(tdir, f)):
                    with open(os.path.join(tdir, f), encoding="utf-8") as fh:
                        named |= set(re.findall(r"LICENSES/([\w+-]+(?:\.[\w+-]+)*)", fh.read()))
            have = set(os.listdir(lic))
            if not named:
                errs.append("reference/LICENSES/ is there but no listed design names a file in it")
            if have - named:
                errs.append(f"reference/LICENSES/ holds files no listed design names: {sorted(have - named)}")
            if named - have:
                errs.append(f"a listed design names licence texts reference/LICENSES/ does not hold: "
                            f"{sorted(named - have)}")
            listed.add("LICENSES")
        stray = sorted(set(on_disk) - listed)
        if stray:
            errs.append(f"reference/ holds files task.json does not list: {stray}")
        good &= record("layout", f"tasks/{t}/task.json", not errs,
                       "; ".join(errs) or f"{status}, input drive {drive}"
                       + ("" if "input_drive" in task else " (the default)"))
    # expected.json <-> disk
    for t in tasks:
        task = task_json(t)
        e = expected["tasks"].get(t)
        errs = []
        if e is None:
            good &= record("layout", f"expected.json {t}", False, "task missing")
            continue
        refs = ({os.path.basename(task["draft_reference"]["sv"])[:-3]}
                if task.get("status") == "draft"
                else {os.path.basename(r["sv"])[:-3] for r in task["references"]})
        if set(e["references"]) != refs:
            errs.append(f"references {sorted(e['references'])} != task.json's {sorted(refs)}")
        for s_, x in e["references"].items():
            twin = x.get("same_design_as")
            if twin and (twin not in e["references"] or not filecmp.cmp(
                    design_path(t, "references", s_, x), design_path(t, "references", twin, {}),
                    shallow=False)):
                errs.append(f"reference {s_} is not byte-identical to {twin}")
        for kind, sub in (("negatives", "negative"), ("baselines", "baselines"),
                          ("attacks", "attacks")):
            d = os.path.join(SVGOLF, "tests", t, sub)
            disk = {f[:-3] for f in os.listdir(d) if f.endswith(".sv")} if os.path.isdir(d) else set()
            listed = {s for s, x in e.get(kind, {}).items() if not x.get("sv")}
            if disk != listed:
                errs.append(f"{sub}/: on disk {sorted(disk)} but expected.json lists {sorted(listed)}")
            for s, x in e.get(kind, {}).items():
                if not os.path.isfile(design_path(t, kind, s, x)):
                    errs.append(f"{kind} {s}: no file {rel(design_path(t, kind, s, x))}")
                # every baseline is proved (decided 2026-11-12): its proof file is on disk (`baseline-proofs` checks it)
                if kind == "baselines" and not (x.get("lean") and os.path.isfile(os.path.join(SVGOLF, "tests", t,
                                                                                               x["lean"]))):
                    errs.append(f"baselines {s}: no proof file (`lean` {x.get('lean')!r}): a baseline without a proof "
                                "cannot be shown, so it is not a baseline (tests/<task>/unproved/ holds test material)")
        good &= record("layout", f"tests/expected.json {t}", not errs, "; ".join(errs) or "complete")
    extra = sorted(set(expected["tasks"]) - set(tasks_on_disk()))
    if extra:
        good &= record("layout", "tests/expected.json", False, f"tasks not on disk: {extra}")
    # the pinned flow the expected scores were measured with
    flow, want = current_flow(), expected.get("flow", {})
    diff = [k for k in flow if flow[k] != want.get(k)]
    good &= record("layout", "tests/expected.json flow = the pinned flow", not diff,
                   "Yosys version and the sha256 of canon.ys, svgolf.ys, ge.json" if not diff
                   else f"differs in {diff}: the expected scores are for another flow "
                   "(--update-scores after a deliberate change)")
    # the clocked flow's pin (decided 2026-11-07): the site compares a clocked task's records with it
    flow, want = current_flow("seq"), expected.get("flow_seq", {})
    diff = [k for k in flow if flow[k] != want.get(k)]
    good &= record("layout", "tests/expected.json flow_seq = the pinned clocked flow", not diff,
                   "Yosys version and the sha256 of canon.ys, svgolf_seq.ys, ge_seq.json" if not diff
                   else f"differs in {diff}: the clocked records are compared with another flow "
                   "(--update-scores after a deliberate change)")
    missing = [p for p in expected.get("canonical_layout", {}).get("designs", {})
               if not os.path.isfile(os.path.join(SVGOLF, p))]
    good &= record("layout", "tests/expected.json canonical_layout designs exist", not missing,
                   ", ".join(missing))
    # no extractor output outside .lake (and no stale old layout)
    stray = []
    for root, dirs, names in os.walk(SVGOLF):
        dirs[:] = [d for d in dirs if d not in (".lake", "__pycache__")
                   and not (root == SVGOLF and d == "design")      # a scratch area of regenerable studies
                   and not dev_only(rel(os.path.join(root, d)) + "/x")]   # development-only directories
        stray += [rel(os.path.join(root, n)) for n in names
                  if n.endswith(".sv.json") or n.endswith(".probes.json")]
    good &= record("layout", "no extractor output outside .lake", not stray, ", ".join(stray[:5]))
    tdir = os.path.join(SVGOLF, "tasks")
    old = [rel(os.path.join(tdir, f)) for f in os.listdir(tdir)
           if not os.path.isdir(os.path.join(tdir, f))]   # tasks/ holds task directories only
    old += [rel(os.path.join(SVGOLF, "tasks", t, d)) for t in tasks_on_disk()
            for d in ("negative", "validate", "baselines", "results")
            if os.path.exists(os.path.join(SVGOLF, "tasks", t, d))]
    good &= record("layout", "old layout gone", not old, ", ".join(old))
    # aggregators
    with open(os.path.join(SVGOLF, "tasks.lean")) as fh:
        tl = fh.read()
    with open(os.path.join(SVGOLF, "tests.lean")) as fh:
        sl = fh.read()
    miss = [f"tasks.{t}.Spec" for t in tasks_on_disk() if f"import tasks.{t}.Spec\n" not in tl]
    miss += [f"tests.{t}.negative.Refute" for t in tasks_on_disk()
             if os.path.isfile(os.path.join(HERE, t, "negative", "Refute.lean"))
             and f"tests.{t}.negative.Refute" not in PENDING_REFUTES
             and f"import tests.{t}.negative.Refute\n" not in sl]
    # a pending refutation is a file on disk that tests.lean does NOT import (the negatives step builds it)
    miss += [f"{m} (PENDING_REFUTES: " + ("no such file" if not os.path.isfile(os.path.join(SVGOLF, pin[0]))
                                          else "imported by tests.lean") + ")"
             for m, pin in PENDING_REFUTES.items()
             if not os.path.isfile(os.path.join(SVGOLF, pin[0])) or f"import {m}\n" in sl]
    good &= record("layout", "tasks.lean / tests.lean import every Spec / Refute", not miss,
                   ", ".join(miss))
    # a pending check.py row is a negative of tests/expected.json whose stage there is not the pinned one
    stale = [f"{k} ({'no such negative' if want is None else 'expected.json already says ' + want})"
             for k, pin in PENDING_STAGES.items()
             for want in [expected["tasks"].get(k.split("/")[0], {}).get("negatives", {})
                          .get(k.split("/")[1], {}).get("stage")]
             if want in (None, pin[0])]
    good &= record("layout", "PENDING_STAGES name negatives of tests/expected.json at another stage", not stale,
                   ", ".join(stale))
    # the one-width generated netlists (test material, shown nowhere on the site: no proof of a task's statement can
    # exist for a design right at one width) are the generators' output, byte for byte
    proc = subprocess.run([PY, os.path.join(HERE, "mul", "unproved", "gen_dadda.py"), "--check"],
                          capture_output=True, text=True)
    good &= record("layout", "gen_dadda.py --check", proc.returncode == 0,
                   (proc.stdout + proc.stderr).strip()[-200:])
    # clmul's flat netlists are generated (the generator's emission order is their canon): up to date
    gen = os.path.join(HERE, "clmul", "unproved", "gen_clmul.py")
    if "clmul" in tasks and os.path.isfile(gen):
        proc = subprocess.run([PY, gen, "--check"], capture_output=True, text=True)
        good &= record("layout", "gen_clmul.py --check", proc.returncode == 0,
                       (proc.stdout + proc.stderr).strip()[-200:])
    # aes_sbox's reference proof, and the proof of its depth-16 baseline, are generated from their netlists: up to date
    for name in ("gen_bp_proof.py", "gen_d16_proof.py"):
        gen = os.path.join(HERE, "aes_sbox", "validate", name)
        if "aes_sbox" in tasks and os.path.isfile(gen):
            proc = subprocess.run([PY, gen, "--check"], capture_output=True, text=True)
            good &= record("layout", f"{name} --check", proc.returncode == 0,
                           (proc.stdout + proc.stderr).strip()[-200:])
    # the proof time limits follow the rule from the recorded cold runs (README.md, "Proof
    # effort"): score/time_limits.py --check
    proc = subprocess.run([PY, os.path.join(SVGOLF, "score", "time_limits.py"), "--check"],
                          capture_output=True, text=True)
    good &= record("layout", "time_limit_s of every task = score/time_limits.py's rule",
                   proc.returncode == 0,
                   "every limit is 300 CPU s; every reference is measured in CPU seconds and none is over it"
                   + "".join(f"; {ln.split(': ', 1)[1]}" for ln in proc.stdout.splitlines()
                             if ln.startswith("time_limits.py: over the"))
                   if proc.returncode == 0 else (proc.stdout + proc.stderr).strip()[-400:])
    return good


# ---------------------------------------------------------------------------
# build, unit
# ---------------------------------------------------------------------------

def lssv_imports():
    """The `LeanModels.Sv.*` modules that proofs under tasks/*/reference and
    tests/*/{negative,attacks,baselines} import: check.py builds a submission's own imports
    unless the runner passes --no-trusted-build, and the runner does, so the build
    step must (a tactic module nobody built reads as 'object file ... does not exist')."""
    mods = set()
    for pat in ("tasks/*/reference/*.lean", "tests/*/negative/*.lean", "tests/*/attacks/*.lean",
                "tests/*/baselines/*.lean", "tests/imports/*.lean"):
        for f in glob.glob(os.path.join(SVGOLF, pat)):
            with open(f) as fh:
                mods.update(re.findall(r"^import (LeanModels\.Sv\.\w+)", fh.read(), re.M))
    return sorted(mods)


def step_build():
    t0 = time.time()
    proc = subprocess.run(WRAP + ["lake", "build"], cwd=SVGOLF, capture_output=True, text=True)
    if proc.returncode == 0 and lssv_imports():
        proc = subprocess.run(WRAP + ["lake", "build"] + lssv_imports(), cwd=SVGOLF,
                              capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    m = re.findall(r"Build completed successfully \((\d+) jobs\)", out)
    built = sorted(set(re.findall(r"Built (tests\.\S+)", out)))
    detail = (f"{m[-1]} jobs" if m else "") + (f"; re-elaborated {', '.join(built)}" if built else "")
    if proc.returncode != 0:
        detail = "lake build failed:\n" + out[-3000:]
    return record("build", "lake build (SvGolf, tasks, tests)", proc.returncode == 0, detail,
                  time.time() - t0)


def step_unit():
    good = True
    for label, cmd in (("score/test_score.py", [PY, "score/test_score.py"]),
                       ("score/test_srcgate.py", [PY, "score/test_srcgate.py"]),
                       ("score/banlist.py --selftest", [PY, "score/banlist.py", "--selftest"]),
                       ("score/fourstate.py --selftest",
                        [PY, "score/fourstate.py", "--selftest"]),
                       ("tests/imports/test_allowlist.py",
                        [PY, "tests/imports/test_allowlist.py"]),
                       # WP-G S1b gate d: the reference proof of `add_proc` IS the proof of `add_proc_m`
                       ("tests/add/same_proof.py", [PY, "tests/add/same_proof.py"]),
                       ("tests/add/same_proof.py --selftest",
                        [PY, "tests/add/same_proof.py", "--selftest"]),
                       # the Newton reference of `fdivp` copies D3's math layer and shared glue: unchanged
                       ("tests/fdivp/shared_sections.py", [PY, "tests/fdivp/shared_sections.py"]),
                       ("tests/fdivp/shared_sections.py --selftest",
                        [PY, "tests/fdivp/shared_sections.py", "--selftest"]),
                       ("tests/checker/test_advisories.py",
                        [PY, "tests/checker/test_advisories.py"]),
                       ("tests/checker/test_design_stage.py",
                        [PY, "tests/checker/test_design_stage.py"]),
                       # `check.py --lift-banlist` (no Lean: a fake Lean): the banned baselines reach the proof
                       # stages, the plain banlist still rejects them, and a lifted result is never a record
                       ("tests/checker/test_lift_banlist.py",
                        [PY, "tests/checker/test_lift_banlist.py"]),
                       ("tests/checker/test_import_packages.py",
                        [PY, "tests/checker/test_import_packages.py"]),
                       # check/layout.py: svGolf inside lean-surfaces and standalone, on synthetic trees
                       ("tests/checker/test_layout.py", [PY, "tests/checker/test_layout.py"]),
                       ("tests/checker/test_slang_errors.py",
                        [PY, "tests/checker/test_slang_errors.py"]),
                       # the clocked kinds' front end: gate rules, latency header, goals (no Lean)
                       ("tests/checker/test_clocked.py", [PY, "tests/checker/test_clocked.py"]),
                       # the clocked score, post-synthesis check and negatives (real Yosys/Verilator/ls-sv)
                       ("tests/checker/test_clocked_post.py", [PY, "tests/checker/test_clocked_post.py"]),
                       # the unknown-constant rule on hand-written netlists, as Yosys's own reader shows them
                       ("tests/checker/test_postsynth_unknown.py", [PY, "tests/checker/test_postsynth_unknown.py"]),
                       # the loop rule bit by bit, and merged flip-flops' bit aliases (UNOPTFLAT waived)
                       ("tests/checker/test_postsynth_loops.py", [PY, "tests/checker/test_postsynth_loops.py"]),
                       ("score/time_limits.py --selftest",
                        [PY, "score/time_limits.py", "--selftest"]),
                       # the sky130 PPA columns: the real-library tests skip when the pinned liberty
                       # is absent (`python3.12 score/ppa.py --fetch-liberty`); where it is present
                       # main() sets SVGOLF_PPA_REQUIRE_LIB=1 so they cannot skip silently
                       ("score/test_ppa.py", [PY, "score/test_ppa.py"]),
                       # ppa.py's STA against OpenSTA's own numbers, recorded (the 11/04 STA study)
                       ("score/test_ppa_opensta.py", [PY, "score/test_ppa_opensta.py"]),
                       # the asap7 alternative (`ppa.py --pdk asap7`): a synthetic two-file library always; the
                       # real-library tests skip when the five pinned files are absent (SVGOLF_ASAP7_LIB, or
                       # `python3.12 score/ppa.py --pdk asap7 --fetch-liberty`; SVGOLF_PPA_REQUIRE_ASAP7=1: no skip)
                       ("score/test_ppa_asap7.py", [PY, "score/test_ppa_asap7.py"]),
                       # the routed course's run tools (score/pnr/) offline on stored run data: the job files of
                       # every committed run, the container command, the collector reproducing a committed table
                       ("tests/pnr/test_pnr_tools.py", [PY, "tests/pnr/test_pnr_tools.py"]),
                       # the reference-against-routed equivalence job (a tool, not pinned): its configuration and
                       # its log reader on the negative control's stored logs
                       ("tests/pnr/test_lec.py", [PY, "tests/pnr/test_lec.py"]),
                       # check.py's `--ppa` modes, the absent-liberty path, the byte-identity of the
                       # default result and the tripwire (no Lean: a fake Lean for the design stage)
                       ("tests/checker/test_ppa_wiring.py",
                        [PY, "tests/checker/test_ppa_wiring.py"]),
                       # WP-S: the scrubbed environment of every child process (and the lint that
                       # keeps it so)
                       ("tests/sandbox/test_env.py", [PY, "tests/sandbox/test_env.py"]),
                       # the sandbox itself: profile and bwrap-argument generation, the supervisor's limits,
                       # the self-test, `configure`, the Lean plumbing (stubbed supervisor), and the real
                       # mechanism on small commands (skipped where there is none); then the tools (Yosys
                       # `$readmemh`, a Verilator model's `$system`) on designs the source gate would refuse
                       ("tests/sandbox/test_sandbox.py", [PY, "tests/sandbox/test_sandbox.py"]),
                       ("tests/sandbox/test_tools.py", [PY, "tests/sandbox/test_tools.py"]),
                       # the site generator (site/build.py): an offline build checked as a whole, and its parts
                       ("tests/site (the site generator)",
                        [PY, "-m", "unittest", "discover", "-s", "tests/site"])):
        t0 = time.time()
        proc = subprocess.run(cmd, cwd=SVGOLF, capture_output=True, text=True)
        out = (proc.stdout + proc.stderr).strip().splitlines()
        good &= record("unit", label, proc.returncode == 0,
                       (out[-1] if out else "") if proc.returncode == 0 else "\n".join(out[-30:]),
                       time.time() - t0)
    return good


def step_comparator():
    """check/Comparator.lean on a hand-built module chain, with real Lean (about a minute), its point 6,
    the re-verification of `bv_decide` axioms (tests/checker/test_bv_decide.py, about two minutes), and rule 3's
    Python twin against the Lean `xsafeB` on tests/seq_counter/xsafe/ and on the arbiter's designs
    (tests/checker/test_xsafe_twin.py)."""
    good = True
    for script in ("tests/checker/test_comparator.py", "tests/checker/test_bv_decide.py",
                   "tests/checker/test_xsafe_twin.py"):
        t0 = time.time()
        proc = subprocess.run([PY, script], cwd=SVGOLF, capture_output=True, text=True)
        out = (proc.stdout + proc.stderr).strip().splitlines()
        good &= record("comparator", script, proc.returncode == 0,
                       (out[-1] if out else "") if proc.returncode == 0 else "\n".join(out[-30:]),
                       time.time() - t0)
    return good


# ---------------------------------------------------------------------------
# leaderboard: Lean-free and fast (README.md, "Leaderboard")
# ---------------------------------------------------------------------------

def step_leaderboard():
    """The leaderboard's own tests, and the integrity of the committed
    records, of the ASAP7 view's columns (leaderboard/asap7/, decided
    2026-11-09: offline, every entry bound to its design) and of the designs at
    other sizes (leaderboard/sizes/, 2026-11-13: offline, the scoring size equal
    to every record's own columns). None runs Lean or Yosys."""
    good = True
    for label, cmd in (("tests/leaderboard/test_leaderboard.py",
                        [PY, "tests/leaderboard/test_leaderboard.py"]),
                       ("leaderboard.py verify --offline (leaderboard/data)",
                        [PY, "leaderboard/leaderboard.py", "verify", "--offline"]),
                       ("leaderboard.py asap7 (leaderboard/asap7, offline)",
                        [PY, "leaderboard/leaderboard.py", "asap7"]),
                       ("tests/leaderboard/test_sizes.py", [PY, "tests/leaderboard/test_sizes.py"]),
                       ("leaderboard.py sizes (leaderboard/sizes, offline)",
                        [PY, "leaderboard/leaderboard.py", "sizes"])):
        t0 = time.time()
        proc = subprocess.run(cmd, cwd=SVGOLF, capture_output=True, text=True)
        out = (proc.stdout + proc.stderr).strip().splitlines()
        summary_line = next((ln for ln in reversed(out) if ln.startswith(("Ran ", "verify "))),
                            out[-1] if out else "")
        good &= record("leaderboard", label, proc.returncode == 0,
                       summary_line if proc.returncode == 0 else "\n".join(out[-30:]),
                       time.time() - t0)
    return good


# ---------------------------------------------------------------------------
# modes: the post-synthesis light/full selection (WP-C2); no Lean
# ---------------------------------------------------------------------------

def postsynth_cli(args_, env_extra=None, unset=True):
    """check/postsynth.py as a command (the standalone research entry); returns
    (exit status, parsed JSON or None, stderr tail)."""
    env = dict(os.environ)
    if unset:
        env.pop("SVGOLF_POSTSYNTH", None)
    env.update(env_extra or {})
    proc = subprocess.run([PY, os.path.join(SVGOLF, "check", "postsynth.py")] + args_,
                          capture_output=True, text=True, env=env, cwd=SVGOLF)
    try:
        out = json.loads(proc.stdout)
    except ValueError:
        out = None
    return proc.returncode, out, (proc.stdout + proc.stderr)[-300:]


def step_modes(tasks, expected, args):
    """The light and full post-synthesis modes through check/postsynth.py: the record says
    which ran; the full record is today's (`vectors == full_vectors`); the light record is
    a smaller set within the task's `light_vectors` that knows the full set's size; both
    share the seed; and the command line and $SVGOLF_POSTSYNTH select the mode (the flag
    wins, a typo is an error, the default is light)."""
    good = True
    cases = [("_example", "tasks/_example/reference/band.sv", ("full", "light")),
             ("add", "tasks/add/reference/add_n.sv", ("full", "light")),
             ("mul", "tasks/mul/reference/mul_n.sv", ("light",))]
    for t, sv_rel, modes in cases:
        if t not in tasks:
            continue
        task = task_json(t)
        cfg = postsynth.config(task)
        tdir = os.path.join(SVGOLF, "tasks", t)
        sv = os.path.join(SVGOLF, sv_rel)
        recs = {}
        for mode in modes:
            t0 = time.time()
            with tempfile.TemporaryDirectory(prefix="svgolf-modes-") as work:
                try:
                    recs[mode] = postsynth.check_design(tdir, sv, work, mode=mode)
                except Exception as e:   # noqa: BLE001  (reported)
                    good &= record("modes", f"{t} {mode}", False,
                                   f"{type(e).__name__}: {str(e).splitlines()[0][:200]}")
                    continue
            r = recs[mode]
            if mode == "full":
                ok = (r.get("mode") == "full" and r["vectors"] == r["full_vectors"]
                      and "full_counts" not in r and "light_vectors" not in r
                      and r["mismatches"] == 0)
                what = f"{r['vectors']} vectors (= the full set), {r['seconds']} s"
            else:
                ok = (r.get("mode") == "light" and r["mismatches"] == 0
                      and r["vectors"] <= cfg["light_vectors"] and r["vectors"] < r["full_vectors"]
                      and r["light_vectors"] == cfg["light_vectors"]
                      and r["full_counts"]["random"] >= r["random"]
                      # the classes taken sum to the set before duplicates drop
                      and r["fixed"] + r["task_corners"] + r["harvest_vectors"] + r["random"]
                      >= r["vectors"])
                what = (f"{r['vectors']} of the full set's {r['full_vectors']} vectors "
                        f"(budget {cfg['light_vectors']}), {r['seconds']} s")
            good &= record("modes", f"{t} {mode}", ok, what, time.time() - t0)
        if len(recs) == 2:
            f, l = recs["full"], recs["light"]
            ok = (f["seed"] == l["seed"] and l["full_vectors"] == f["vectors"]
                  and l["full_counts"] == {"fixed": f["fixed"], "task_corners": f["task_corners"],
                                           "harvest_vectors": f["harvest_vectors"],
                                           "random": f["random"]})
            good &= record("modes", f"{t} both modes agree on seed and the full set",
                           ok, f"seed {f['seed'][:12]}, full set {f['vectors']} vectors")
    if "_example" in tasks:
        base = ["--task", "tasks/_example", "tasks/_example/reference/band.sv"]
        for label, cli, env, want in (
                ("default (no flag, no variable)", [], {}, "light"),
                ("$SVGOLF_POSTSYNTH=full", [], {"SVGOLF_POSTSYNTH": "full"}, "full"),
                ("--mode light beats $SVGOLF_POSTSYNTH=full", ["--mode", "light"],
                 {"SVGOLF_POSTSYNTH": "full"}, "light")):
            t0 = time.time()
            rc, out, tail = postsynth_cli(base + cli, env)
            got = ((out or {}).get("record") or {}).get("mode")
            good &= record("modes", f"postsynth.py {label}", rc == 0 and got == want,
                           f"exit {rc}, mode {got} (want {want})", time.time() - t0)
        rc, out, tail = postsynth_cli(base, {"SVGOLF_POSTSYNTH": "fast"})
        good &= record("modes", "postsynth.py $SVGOLF_POSTSYNTH=fast is an error, not light",
                       rc == 2 and "SVGOLF_POSTSYNTH" in tail, f"exit {rc}: {tail.strip()[-120:]}")
    return good


# ---------------------------------------------------------------------------
# canon: the canonical scoring flow makes the score a function of the circuit
# ---------------------------------------------------------------------------

def step_canon(tasks, expected, args):
    sys.path.insert(0, os.path.join(HERE, "canon"))
    import variants
    canon = expected.setdefault("canonical_layout", {}).setdefault("designs", {})
    good = True
    with tempfile.TemporaryDirectory(prefix="svgolf-canon-") as tmp:
        for path, want in canon.items():
            if path.split("/")[1] not in tasks:
                continue
            top, point = want["top"], parse_point(want["point"])
            t0 = time.time()
            src = os.path.join(SVGOLF, path)
            base = score.score([src], top, point)
            vs = variants.make_variants(src, top, os.path.join(tmp, os.path.basename(path)))
            same_rtlil, same_only, bad = [], [], []
            commute = None
            for v, vpath in vs.items():
                kind = variants.VARIANTS[v][0]
                try:
                    r = score.score([vpath], top, point)
                except score.ScoreError as e:
                    bad.append(f"{v}: {str(e).splitlines()[0][:100]}")
                    continue
                got = {k: r[k] for k in ("area_ge", "area_mge", "depth", "num_gates", "gates")}
                if kind == "commute":
                    commute = got
                    continue
                if not same_score(got, base):
                    bad.append(f"{v} ({kind}): {score_diff(got, base)}")
                elif kind in ("layout", "rename") and r["rtlil_sha256"] != base["rtlil_sha256"]:
                    bad.append(f"{v} ({kind}): same score but a different canonical RTLIL")
                else:
                    (same_rtlil if r["rtlil_sha256"] == base["rtlil_sha256"]
                     else same_only).append(v)
            nl = len([v for v in vs if variants.VARIANTS[v][0] in ("layout", "rename")])
            good &= record("canon", f"{path} at {want['point']}", not bad,
                           (f"{show_score(base)}: {len(same_rtlil)} variants with a byte-identical "
                            f"canonical RTLIL ({nl} layout/rename among them), {len(same_only)} "
                            "reorderings with the same score") if not bad
                           else "; ".join(bad[:4]), time.time() - t0)
            if commute is not None:
                if args.update_scores:
                    want["commute"] = commute
                    record("canon", f"{path} commuted operands", True,
                           f"recorded {show_score(commute)}")
                else:
                    ok = same_score(commute, want.get("commute", {}))
                    good &= record("canon", f"{path} commuted operands", ok,
                                   f"{show_score(commute)} (recorded residual: expression "
                                   "structure is scored)" if ok
                                   else score_diff(commute, want.get("commute", {})))
    return good


# ---------------------------------------------------------------------------
# references, drafts, negatives, baselines
# ---------------------------------------------------------------------------

PPA_GOLD = []


def ppa_gold():
    """(designs by `src`, all designs, goldens): score/tests/ppa/, the goldens of the PPA columns. The designs of
    designs.json (references and baselines, goldens in expected_ppa.json) and of idioms.json (the netlist-reader idioms,
    task "idioms", goldens in expected_idioms.json). `goldens["identity"]`: (file name, the golden file) pairs, for the
    check that each was recorded under the pinned liberty and `ppa_version`. `goldens["mapped"]`: the goldens of flow A1'
    (WP-X4) of all of those designs, from expected_ppa_mapped.json; `goldens["mapped_file"]` the file itself."""
    if not PPA_GOLD:
        d = os.path.join(SVGOLF, "score", "tests", "ppa")
        designs, gold, ident = [], {}, []
        for dfile, gfile in (("designs.json", "expected_ppa.json"), ("idioms.json", "expected_idioms.json")):
            g = load_json(os.path.join(d, gfile))
            designs += load_json(os.path.join(d, dfile))["designs"]
            gold.update(g["designs"])
            ident.append((gfile, g))
        mapped = load_json(os.path.join(d, "expected_ppa_mapped.json"))
        PPA_GOLD.append(({x["src"]: x for x in designs}, designs,
                         {"designs": gold, "identity": ident, "mapped": mapped["designs"], "mapped_file": mapped}))
    return PPA_GOLD[0]


def ppa_vs_gold(block, sres, g):
    """The differences between a `ppa` block (with the score result it was weighed with) and the golden entry `g`
    of score/tests/ppa/expected_ppa.json: (GE, depth, gates) of the GE columns and (um^2, ps, levels, cells, the scored
    and the repaired netlist's hashes) of the sky130 ones."""
    got = {"area_ge": sres["area_ge"], "depth": sres["depth"], "gates": sres["num_gates"],
           "area_e4um2": block.get("area_e4um2_sky130"), "delay_ps": block.get("delay_ps_sky130"),
           "unit_depth": block.get("unit_depth"), "cells": block.get("cells_sky130"),
           "netlist_sha256": block.get("netlist_sha256"), "repaired_sha256": (block.get("repair") or {}).get("netlist_sha256")}
    return [f"{k} {got[k]!r} (golden {g[k]!r})" for k in got if got[k] != g[k]]


_PPA_LIB = []


def ppa_lib():
    """(Liberty, Pins) of the pinned liberty, opened once (0.1 s); only called where ppa_state() is "present"."""
    if not _PPA_LIB:
        _PPA_LIB.append(ppa.open_library())
    return _PPA_LIB[0]


def ppa_block_problems(block, sres, task=None):
    """What a weighed `ppa` block must satisfy beyond its numbers: weighed at all, under the pinned inputs, in
    agreement with the score result of the same run (the scorer's `ltp -noff` depth is the scored netlist's unit depth;
    its gate count is the scored netlist's cell count before the repair, `repair.cells_before`), and internally consistent
    in the columns the goldens do not pin: `area_um2_sky130` is `area_e4um2_sky130` / 10^4; the cell histogram (of the
    REPAIRED netlist, sky130_a0_v2) sums to `cells_sky130`, and its areas in the live liberty sum to `area_e4um2_sky130`;
    `setup` (its `input_drive` the task's, sky130_a0_v3), `liberty_file` and the repair's method are the pins file's; the
    legality audit found nothing; `critical` has its shape (`output` a name or null, `edge` r or f, `cells` a count within the netlist's)."""
    if block.get("available") is not True:
        return [f"not weighed: {block.get('reason')}"]
    lib, pins = ppa_lib()
    p = []
    for k, want in (("ppa_version", pins.version), ("ppa_pins_sha256", pins.sha256),
                    ("liberty_sha256", pins.lib["sha256"]), ("unit_depth", sres["depth"]),
                    ("ppa_script_sha256", ppa.sha256_file(ppa.__file__)),
                    ("liberty_file", pins.lib_file()),
                    ("setup", {"pi_slew_ps": round(pins.pi_slew_ns * 1000), "input_drive": ppa.input_drive_of(task, pins),
                               "po_load_ff": round(pins.po_load_pf * 1000), "wires": "none", "tables": "no extrapolation"})):
        if block.get(k) != want:
            p.append(f"{k} {block.get(k)!r} is not {want!r}")
    rep = block.get("repair") or {}
    if rep.get("method") != pins.repair_method:
        p.append(f"repair {rep!r} is not the pinned repair ({pins.repair_method!r})")
    if rep.get("cells_before") != sres["num_gates"]:
        p.append(f"repair.cells_before {rep.get('cells_before')} vs score gates {sres['num_gates']}")
    leg = block.get("legality") or {}
    if any(leg.get(k) != 0 for k in ("over_max_capacitance", "over_max_transition", "table_reads_outside")):
        p.append(f"legality {leg!r}: a weighed netlist must be legal")
    e4 = block.get("area_e4um2_sky130")
    if not isinstance(e4, int) or block.get("area_um2_sky130") != e4 / 10000:
        p.append(f"area_um2_sky130 {block.get('area_um2_sky130')!r} is not area_e4um2_sky130 {e4!r} / 10000")
    hist = block.get("cell_hist_sky130")
    if not isinstance(hist, dict) or sum(hist.values()) != block.get("cells_sky130"):
        p.append(f"cell_hist_sky130 {hist!r} does not sum to cells_sky130 {block.get('cells_sky130')!r}")
    else:
        try:
            # a clocked block's flop (dfxtp_1) is weighed by ppa.FlopTiming: its CLK->Q arc is not a gate's
            by_cell = sum(n * (ppa.FlopTiming(lib, pins).area_e4 if c == ppa.FLOP_CELL
                               else lib.cell(pins.prefix + c).area_e4) for c, n in hist.items())
        except ppa.PpaError as e:
            p.append(f"cell_hist_sky130 names a cell the liberty does not have: {e}")
        else:
            if by_cell != e4:
                p.append(f"cell_hist_sky130 weighs {by_cell} (1e-4 um^2) in the liberty, area_e4um2_sky130 is {e4}")
    crit = block.get("critical")
    if not (isinstance(crit, dict) and set(crit) == {"output", "edge", "cells"}
            and (crit["output"] is None or isinstance(crit["output"], str)) and crit["edge"] in ("r", "f", None)
            and isinstance(crit["cells"], int) and 0 <= crit["cells"] <= block.get("cells_sky130", 0)):
        p.append(f"critical {crit!r} is not {{output, edge r/f, cells <= cells_sky130}}")
    return p


def ppa_mapped_vs_gold(m, g):
    """The differences between a `ppa.mapped` block (flow A1') and the golden entry `g` of
    score/tests/ppa/expected_ppa_mapped.json: the canonical RTLIL it read, (um^2, ps, cells, cell levels, buffers,
    inverters, constants) and the hash of the mapped netlist."""
    got = {"rtlil_sha256": m.get("rtlil_sha256"), "area_e4um2": m.get("area_e4um2_sky130_mapped_v1"),
           "delay_ps": m.get("mapped_delay_sky130_v1"), "cells": m.get("mapped_cells_sky130_v1"),
           "levels": m.get("mapped_levels_sky130_v1"), "buffers": m.get("mapped_buffers_sky130_v1"),
           "inverters": m.get("mapped_inverters_sky130_v1"), "constants": m.get("constants"),
           "netlist_sha256": m.get("netlist_sha256")}
    return [f"mapped {k} {got[k]!r} (golden {g[k]!r})" for k in got if got[k] != g[k]]


def ppa_mapped_block_problems(m, rtlil_sha256=None):
    """What a weighed `ppa.mapped` block (flow A1') must satisfy beyond its numbers: mapped at all, under the pinned
    inputs (version, liberty, pins, script, the live Yosys and ABC builds, the equivalence sample), reading the canonical RTLIL
    of the same score run (`rtlil_sha256`, when given), and internally consistent: area in um^2 is 1e-4 um^2 / 10^4, the
    histogram sums to the cell count and, priced cell by cell in the live liberty (+ the one tie cell when a constant is used),
    to the area; the buffer and inverter counts are the histogram's; `setup`, `liberty_file` are the pins file's;
    `critical` has its shape."""
    if not (isinstance(m, dict) and m.get("available") is True):
        return [f"not mapped: {(m or {}).get('reason', 'no `mapped` object')}"]
    lib, pins = ppa_lib()
    mp = ppa.MappedPins(pins)
    p = []
    for k, want in (("ppa_mapped_version", mp.version), ("ppa_mapped_pins_sha256", mp.sha256),
                    ("ppa_mapped_script_sha256", mp.script_sha256), ("ppa_pins_sha256", pins.sha256),
                    ("liberty_sha256", pins.lib["sha256"]), ("liberty_file", pins.lib_file()),
                    ("ppa_script_sha256", ppa.sha256_file(ppa.__file__)),
                    ("yosys_version", score.yosys_version(score.yosys_bin())),
                    ("abc_version", ppa.abc_version(score.yosys_bin())),
                    ("equivalence", {"vectors": mp.equiv_vectors, "seed": mp.equiv_seed}),
                    ("setup", {"pi_slew_ps": round(pins.pi_slew_ns * 1000), "po_load_ff": round(pins.po_load_pf * 1000),
                               "wires": "none"})):
        if m.get(k) != want:
            p.append(f"mapped.{k} {m.get(k)!r} is not {want!r}")
    if rtlil_sha256 is not None and m.get("rtlil_sha256") != rtlil_sha256:
        p.append(f"mapped.rtlil_sha256 {m.get('rtlil_sha256')!r} is not the score run's {rtlil_sha256!r}")
    e4 = m.get("area_e4um2_sky130_mapped_v1")
    if not isinstance(e4, int) or m.get("area_um2_sky130_mapped_v1") != e4 / 10000:
        p.append(f"mapped.area_um2_sky130_mapped_v1 {m.get('area_um2_sky130_mapped_v1')!r} is not area_e4um2 {e4!r} / 10000")
    hist = m.get("mapped_cell_hist_sky130_v1")
    if not isinstance(hist, dict) or sum(hist.values()) != m.get("mapped_cells_sky130_v1"):
        p.append(f"mapped cell histogram {hist!r} does not sum to mapped_cells_sky130_v1 {m.get('mapped_cells_sky130_v1')!r}")
    else:
        try:
            by_cell = sum(n * lib.cell(pins.prefix + c).area_e4 for c, n in hist.items())
        except ppa.PpaError as e:
            p.append(f"mapped histogram names a cell the liberty does not have: {e}")
        else:
            if by_cell != e4:
                p.append(f"mapped histogram weighs {by_cell} (1e-4 um^2) in the liberty, area_e4um2 is {e4}")
        if any(ppa.cell_class(pins.prefix + c, pins.prefix) not in ("logic", "tie") for c in hist):
            p.append(f"mapped histogram has cells outside the policy class `logic`: {sorted(hist)}")
        bufs = sum(n for c, n in hist.items() if c.startswith(("buf_", "bufbuf_", "bufinv_")))
        invs = sum(n for c, n in hist.items() if c.startswith("inv_"))
        if (m.get("mapped_buffers_sky130_v1"), m.get("mapped_inverters_sky130_v1")) != (bufs, invs):
            p.append("mapped buffer and inverter counts are not the histogram's")
    crit = m.get("critical")
    if not (isinstance(crit, dict) and set(crit) == {"output", "edge", "cells"}
            and (crit["output"] is None or isinstance(crit["output"], str)) and crit["edge"] in ("r", "f", None)
            and isinstance(crit["cells"], int) and 0 <= crit["cells"] <= m.get("mapped_cells_sky130_v1", 0)
            and m.get("mapped_levels_sky130_v1", 0) <= m.get("mapped_cells_sky130_v1", 0)):
        p.append(f"mapped critical {crit!r} is not {{output, edge r/f, cells <= mapped cells}}")
    return p


def check_reference_ppa(t, stem, sv_rel, res):
    """The wiring of the PPA columns on a reference's REAL check.py result (accepted, run with `--ppa` =
    ppa_mode()): (1) everything but the new key and stage is, character for character, the baseline checker's result
    (the `add` and `aes_sbox` references; goldens in tests/checker/ppa_wiring/); (2) the `ppa` block is weighed,
    consistent with the score of the same run and, where score/tests/ppa/expected_ppa.json has the design, equal to
    its golden (one record per reference; skipped with a message where the pinned liberty is absent)."""
    good = True
    base = {k: v for k, v in res.items() if not k.startswith("_")}     # this runner's own keys (`_seconds`, `_exit`)
    base["stages"] = {k: v for k, v in base["stages"].items() if k != "trusted"}   # a run without --no-trusted-build
    # ... and its completeness verdict, which says whether the run built the trusted modules (check.py
    # `incomplete_reasons`): a function of this runner's flags, not of the design
    base.pop("complete", None)
    base.pop("incomplete", None)
    if byte_identity.FULL_GOLDEN_REFERENCE.get(t) == stem:
        want = byte_identity.golden(t, "full")
        got = byte_identity.render(byte_identity.without_ppa(base))
        diff = list(difflib.unified_diff(want.splitlines(), got.splitlines(), "baseline", "now", lineterm="", n=0))
        good &= record("references", f"{t}/{stem} result = the baseline checker's + the ppa key and stage",
                       not diff,
                       "every key and every deterministic value of the pre-wiring result (tests/checker/ppa_wiring/)"
                       if not diff else "differs:\n" + "\n".join(diff[:14]))
    state = ppa_state()[0]
    if state == "invalid":
        return good      # one loud failure, in the `ppa` step
    if state == "absent":
        if not PPA_NOTED:
            PPA_NOTED.append(True)
            record("references", "sky130 PPA columns of the references", True, ppa_skip_note())
        return good
    block = res.get("ppa") or {}
    sres = {"area_ge": res["score"]["area_ge"], "depth": res["score"]["depth"], "num_gates": res["score"]["num_gates"]}
    probs = ppa_block_problems(block, sres, task_json(t))
    if res.get("stages", {}).get("ppa", {}).get("mode") != "require":
        probs.append(f"stages.ppa.mode is {res.get('stages', {}).get('ppa', {}).get('mode')!r}, not 'require'")
    by_src, _, gold = ppa_gold()
    d = by_src.get(sv_rel)
    detail = ""
    mapped = block.get("mapped") if isinstance(block, dict) else None
    clocked = "ffs" in res["score"]      # a clocked task's result (check.py `score_clocked`)
    if clocked and not probs:
        # the clocked block (PLAN4 Gate 2 step 3): the period of the flops' netlist, its flops the score's, no A1'
        # mapping (check.py weighs a clocked netlist with A0' only); the ranked score is this block's
        s = res["score"]
        if not (block.get("sequential") is True and block.get("flops") == s["ffs"] and "mapped" not in block):
            probs.append(f"clocked block: sequential {block.get('sequential')!r}, flops {block.get('flops')!r} "
                         f"(score ffs {s['ffs']}), mapped {'mapped' in block}")
        if (s.get("area_um2"), s.get("period_ps"), s.get("time_ps")) != (
                block.get("area_um2_sky130"), block.get("delay_ps_sky130"), s.get("cycles", 0) * block.get("delay_ps_sky130", 0)):
            probs.append(f"clocked score {s.get('area_um2')} um^2, {s.get('cycles')} x {s.get('period_ps')} = "
                         f"{s.get('time_ps')} ps is not the ppa block's")
    elif not probs:         # flow A1' (WP-X4): the same checks on the `mapped` sub-object of the same real result
        probs += ppa_mapped_block_problems(mapped, ((res.get("stages") or {}).get("score") or {}).get("rtlil_sha256"))
    if d is not None and not probs:
        probs += ppa_vs_gold(block, sres, gold["designs"][d["name"]])
        probs += ppa_mapped_vs_gold(mapped, gold["mapped"][d["name"]])
        PPA_REFERENCE_NAMES.add(d["name"])
        detail = f"= the golden of {d['name']}: "
    elif not probs:
        detail = "no golden for this design (consistency only): "
    if not probs and clocked:
        detail += (f"{block['area_um2_sky130']} um^2, period {block['delay_ps_sky130']} ps, {block['unit_depth']} levels, "
                   f"{block['cells_sky130']} cells, {block['flops']} flops ({block['ppa_version']}, clocked; "
                   f"stage {res['stages']['ppa']['seconds']} s)")
    elif not probs:
        detail += (f"{block['area_um2_sky130']} um^2, {block['delay_ps_sky130']} ps, {block['unit_depth']} levels, "
                   f"{block['cells_sky130']} cells ({block['ppa_version']}; mapped A1' "
                   f"{mapped['area_um2_sky130_mapped_v1']} um^2, {mapped['mapped_delay_sky130_v1']} ps, "
                   f"{mapped['mapped_cells_sky130_v1']} cells; stage {res['stages']['ppa']['seconds']} s)")
    return good & record("references", f"{t}/{stem} ppa", not probs, detail if not probs else "; ".join(probs))


def step_references(tasks, expected, args):
    good = True
    for t in tasks:
        task = task_json(t)
        if task.get("status") != "ready":
            continue
        tdir = os.path.join(SVGOLF, "tasks", t)
        for r in task["references"]:
            stem = os.path.basename(r["sv"])[:-3]
            want = expected["tasks"][t]["references"][stem]
            res = run_check(tdir, os.path.join(tdir, r["sv"]), os.path.join(tdir, r["lean"]),
                            args.check_extra, ppa_flag=ppa_mode())
            ok = bool(res.get("accepted"))
            ps = (res.get("stages") or {}).get("postsynth") or {}
            clocked = task.get("kind") in checkpy().CLOCKED_KINDS
            psd = (f" (postsynth {ps.get('mode')}: {ps.get('vectors')} vectors agree, "
                   f"{ps.get('seconds')} s; "
                   f"score {(res.get('stages') or {}).get('score', {}).get('seconds')} s)"
                   if ok and ps and not clocked else "")
            good &= record("references", f"{t}/{stem}", ok,
                           verdict(res) + psd + ("" if ok else ": " + first_error(res)),
                           res["_seconds"])
            if ok:
                # the full check ran: today's whole budget (WP-C2), and the design stage
                # tested every probe point for an Unsupported construct (WP-C3)
                if clocked:
                    mok, mdetail = clocked_postsynth_ok(task, ps, res)
                else:
                    mok = (ps.get("mode") == "full" and ps.get("vectors") == ps.get("full_vectors")
                           and "light_vectors" not in ps)
                    mdetail = f"mode {ps.get('mode')}, {ps.get('vectors')} of {ps.get('full_vectors')} vectors"
                good &= record("references", f"{t}/{stem} full postsynth", mok, mdetail)
                pts = len(checkpy().unsupported_check_points(task))
                dok = ((res.get("stages") or {}).get("design") or {}).get(
                    "unsupported_free_points") == pts
                good &= record("references", f"{t}/{stem} no unsupported construct", dok,
                               f"the design stage checked {pts} point(s) of the design"
                               if dok else f"design stage: {(res.get('stages') or {}).get('design')}")
            if ok:
                good &= check_reference_ppa(t, stem, os.path.join("tasks", t, r["sv"]), res)
            if ok and task.get("oracle") and not clocked:     # (a clocked task's oracle is binding: postsynth above)
                # the advisory oracle (check/postsynth.py): a PROVED design computes the task's
                # function, so the oracle must agree on every vector (a mismatch is an oracle bug)
                f = ps.get("functional") or {}
                fok = (f.get("mismatches") == 0 and f.get("checked") == ps.get("vectors")
                       and "unchecked" not in f and "warnings" not in res)
                good &= record("references", f"{t}/{stem} functional", fok,
                               f"{f.get('checked')} of {ps.get('vectors')} vectors agree with "
                               f"{task['oracle']}" if fok else
                               f"advisory oracle disagrees: {f} {res.get('warnings')}")
            spoint = envelope.point_str(task["scoring"]["params"]) or "default"
            if ok and spoint in want.get("scores", {}):
                got = {k: res["score"][k] for k in ("area_ge", "area_mge", "depth", "num_gates",
                                                     "gates") + (CLOCKED_SCORE_KEYS if clocked else ())}
                if args.update_scores:
                    want["scores"][spoint] = got
                else:
                    same = same_score(got, want["scores"][spoint])
                    good &= record("references", f"{t}/{stem} check.py score {spoint}", same,
                                   show_score(got) + ("" if same else " (expected "
                                                      + show_score(want["scores"][spoint]) + ")"))
            elif ok:
                good &= record("references", f"{t}/{stem}", False,
                               f"tests/expected.json has no score at the scoring point {spoint}")
            if not want.get("same_design_as") and not clocked:   # (score.py's comb flow; a clocked task: check.py only)
                good &= check_scores("references", f"{t}/{stem}", os.path.join(tdir, r["sv"]),
                                     task["top"], want.get("scores", {}), args, skip=(spoint,))
    return good


def clocked_postsynth_ok(task, ps, res=None):
    """A clocked reference's post-synthesis record (check/postsynth.py `run_clocked`, PLAN4 Gate 2 step 4): the
    scoring point and every point of task.json's `postsynth.points`, each in full mode with every seed run and no
    failure (the netlist against ls-sv cycle by cycle, and C where done = 1 against the oracle: both binding); for a
    latency kind each point at its own latency (F8, decided 2026-11-08): the kernel's `Submission.lat p` that the
    result records (`latency_at`), the scoring point's the declared n."""
    cfg = postsynth.config(task)
    want = ({envelope.point_str(task["scoring"]["params"]) or "default"}
            | {envelope.point_str(p) or "default" for p in cfg["points"] or []})
    pts = ps.get("points") or []
    lat_at = (res or {}).get("latency_at")
    latency_kind = task.get("kind") in checkpy().LATENCY_KINDS
    bad = [p.get("point") for p in pts if not (p.get("mode") == "full" and p.get("mismatches") == 0
                                                 and len(p.get("seeds") or []) == cfg["seeds"])
           or (latency_kind and not (isinstance(lat_at, dict) and p.get("latency") == lat_at.get(p.get("point"))))]
    if latency_kind and isinstance(lat_at, dict) and \
            lat_at.get(envelope.point_str(task["scoring"]["params"])) != (res or {}).get("latency"):
        bad.append("the scoring point's latency is not the declared one")
    got = {p.get("point") for p in pts}
    ok = got == want and not bad and len(pts) == len(want)
    detail = "; ".join(f"{p.get('point')}: {p.get('mode')}, {len(p.get('seeds') or [])} seeds, "
                       f"{sum(x.get('cycles', 0) for x in p.get('seeds') or [])} cycles, "
                       + (f"latency {p.get('latency')}, " if latency_kind else "")
                       + f"{p.get('mismatches')} failures, {p.get('seconds')} s" for p in pts)
    if bad:
        detail = f"failing: {bad}; " + detail
    if got != want:
        detail = f"points {sorted(got)}, want {sorted(want)}; " + detail
    return ok, detail


def step_drafts(tasks, expected, args):
    good = True
    for t in tasks:
        task = task_json(t)
        if task.get("status") != "draft":
            continue
        tdir = os.path.join(SVGOLF, "tasks", t)
        d = task["draft_reference"]
        stem = os.path.basename(d["sv"])[:-3]
        if not checker_kind(task):
            good &= record("drafts", f"{t}/{stem}", True,
                           f"SKIPPED: check.py has no checker for kind {task.get('kind')!r} yet (a statement draft)")
            continue
        if statement_draft(t, task):
            good &= statement_draft_goalpost(t, task, tdir, stem, args)
            continue
        want = expected["tasks"][t]["references"][stem]
        res = run_check(tdir, os.path.join(tdir, d["sv"]), os.path.join(tdir, d["lean"]),
                        args.check_extra + ["--no-score"])
        ok = not res.get("accepted") and res.get("stage") == want["stage"]
        good &= record("drafts", f"{t}/{stem} with {os.path.basename(d['lean'])}", ok,
                       f"{verdict(res)} (want rejected at {want['stage']}: every earlier stage "
                       "passes)" + ("" if ok else ": " + first_error(res)), res["_seconds"])
        good &= check_scores("drafts", f"{t}/{stem}", os.path.join(tdir, d["sv"]), task["top"],
                             want.get("scores", {}), args)
        # check.py stops a draft before scoring; its goalpost must pass postsynth too
        good &= baseline_postsynth(t, task, f"{t}/{stem}", os.path.join(tdir, d["sv"]),
                                   {"scores": want.get("scores", {})}, args, step="drafts")
    return good


def statement_draft_goalpost(t, task, tdir, stem, args):
    """A statement draft's goalpost through `check.py --unproved` (with its `latency` for a latency kind): every
    stage that needs no proof passes; a clocked kind's postsynth record as `clocked_postsynth_ok` wants it."""
    d = task["draft_reference"]
    lat = ["--latency", str(d.get("latency"))] if task.get("kind") in checkpy().LATENCY_KINDS else []
    res = run_check(tdir, os.path.join(tdir, d["sv"]), None, args.check_extra + ["--unproved"] + lat,
                    ppa_flag=ppa_mode())
    ok = clean_unproved(res)
    detail = "every stage without a proof passes (exit 0)" if ok else f"{verdict(res)} (want a clean unproved run)"
    clocked = task.get("kind") in checkpy().CLOCKED_KINDS
    if ok and clocked:
        ok, detail = clocked_postsynth_ok(task, res["stages"].get("postsynth") or {}, res)
        detail += f"; score {show_score(res['score'])}"
    good = record("drafts", f"{t}/{stem} goalpost --unproved {' '.join(lat)}".rstrip(), ok,
                  detail if ok else f"{detail}: {first_error(res)}", res["_seconds"])
    # the goalpost's ranked score at the scoring point, where tests/expected.json records it (a clocked kind: the
    # sky130 pair of check.py's clocked score, so a change of the design or the flow shows here)
    want = (((args.expected_tasks or {}).get(t) or {}).get("references") or {}).get(stem) or {}
    spoint = envelope.point_str(task["scoring"]["params"]) or "default"
    if res.get("stage") == "unproved" and clocked and spoint in want.get("scores", {}):
        got = {k: res["score"][k] for k in ("area_ge", "area_mge", "depth", "num_gates", "gates") + CLOCKED_SCORE_KEYS}
        if args.update_scores:
            want["scores"][spoint] = got
        else:
            same = same_score(got, want["scores"][spoint])
            good &= record("drafts", f"{t}/{stem} goalpost check.py score {spoint}", same,
                           show_score(got) + ("" if same else " (expected " + show_score(want["scores"][spoint]) + ")"))
    return good


def step_negatives(tasks, expected, args):
    good = True
    for t in tasks:
        task = task_json(t)
        tdir = os.path.join(SVGOLF, "tasks", t)
        if task.get("status") == "draft" and (not checker_kind(task) or statement_draft(t, task)):
            if expected["tasks"][t]["negatives"]:
                good &= record("negatives", t, True, f"SKIPPED: a statement draft (kind "
                               f"{task.get('kind')!r}, no partial proof file)")
            continue
        lean = first_lean(t, task)
        for stem, n in expected["tasks"][t]["negatives"].items():
            sv = design_path(t, "negatives", stem, n)
            # an entry may name its own proof file (`lean`, relative to tests/<task>/): a negative whose
            # point is what a PROOF does with it (WP-G: a refusal by the new tactic elaborators)
            nlean = os.path.join(SVGOLF, "tests", t, n["lean"]) if n.get("lean") else lean
            res = run_check(tdir, sv, nlean, args.check_extra + ["--no-score"])
            if f"{t}/{stem}" in PENDING_STAGES:
                good &= pending_stage(f"{t}/{stem}", n, res)
                good &= check_scores("negatives", f"{t}/{stem}", sv, task["top"], n.get("scores", {}), args)
                continue
            ok = not res.get("accepted") and res.get("stage") == n["stage"]
            if ok and n.get("message_contains"):
                ok = n["message_contains"] in json.dumps(res.get("errors"))
            good &= record("negatives", f"{t}/{stem}", ok,
                           f"{verdict(res)} (want {n['stage']}): "
                           + (first_error(res) if ok else json.dumps(res.get("errors"))[:600]),
                           res["_seconds"])
            good &= check_scores("negatives", f"{t}/{stem}", sv, task["top"],
                                 n.get("scores", {}), args)
        mod = f"tests.{t}.negative.Refute"
        if mod in PENDING_REFUTES:
            good &= pending_refute(mod)
    return good


def pending_stage(key, n, res):
    """One PENDING_STAGES row's check.py result: rejected at the pinned stage (not yet at tests/expected.json's), its
    first error starting as pinned and that error's first Lean error line carrying every pinned phrase (the loader's
    refusal; the errors after it follow from the missing design). Any other result fails the step; one rejected at
    its expected.json stage says the int32 port round has come for it."""
    stage, head, *phrases = PENDING_STAGES[key]
    errors = res.get("errors") or []
    first = errors[0] if errors and isinstance(errors[0], str) else ""
    lean = [ln for ln in first.splitlines() if re.search(r":\d+:\d+: error\b", ln)]
    why = f"pinned until the int32 port round; tests/expected.json: {n['stage']}"
    if not res.get("accepted") and res.get("stage") == n["stage"]:
        return record("negatives", key, False, f"{verdict(res)}, the stage tests/expected.json gives it: drop it from "
                      "PENDING_STAGES (and its module from PENDING_REFUTES)", res["_seconds"])
    ok = (not res.get("accepted") and res.get("stage") == stage and first.startswith(head) and bool(lean)
          and all(ph in lean[0] for ph in phrases))
    return record("negatives", key, ok, f"{verdict(res)} (want {stage}, {why}): "
                  + (lean[0].split(": error", 1)[1].lstrip(": ")[:160] if ok else json.dumps(errors)[:600]),
                  res["_seconds"])


def pending_refute(mod):
    """Build one PENDING_REFUTES module alone: it must FAIL, and its FIRST error must carry every pinned phrase
    (the loader's refusal of its `only_n16.sv`; the errors after it follow from the missing design). One that
    builds, or fails another way first, fails the step."""
    t0 = time.time()
    proc = subprocess.run(WRAP + ["lake", "build", mod], cwd=SVGOLF, capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    label = f"{mod.split('.')[1]}: {mod} (waits for the int32 port round)"
    if proc.returncode == 0:
        return record("negatives", label, False,
                      f"`lake build {mod}` now SUCCEEDS: import it in tests.lean again and drop it from "
                      "PENDING_REFUTES", time.time() - t0)
    phrases = PENDING_REFUTES[mod][1:]
    errors = [ln for ln in out.splitlines() if ln.startswith("error:")]
    if not errors or not all(ph in errors[0] for ph in phrases):
        return record("negatives", label, False, "failed, but its first error is not the pinned refusal "
                      f"{phrases!r}:\n" + ("\n".join(errors[:5]) or out[-1500:])[-1500:], time.time() - t0)
    return record("negatives", label, True, f"fails as pinned ({len(errors)} errors; the first: "
                  + errors[0].split(": ", 1)[1][:160] + ")", time.time() - t0)


def canon_tokens(path):
    canon, findings = envelope.gate(path)
    return None if findings else "".join(canon.split())


def step_baselines(tasks, expected, args):
    good = True
    for t in tasks:
        task = task_json(t)
        ops, task_points = banlist.task_banlist(task)
        for stem, b in expected["tasks"][t]["baselines"].items():
            sv = design_path(t, "baselines", stem, b)
            label = rel(sv)
            good &= check_scores("baselines", label, sv, task["top"], b.get("scores", {}), args)
            if not b.get("scores"):
                record("baselines", f"{label} score", True,
                       "not scored (tests/expected.json says why)")
            points = ([envelope.parse_point(p) for p in b["banlist_points"]]
                      if "banlist_points" in b else task_points)
            t0 = time.time()
            res = banlist.check([sv], task["top"], ops, points)
            hit = bool(res["front"] or res["backstop"])
            ok = (not res["passed"] and hit) if b["banned"] else res["passed"]
            what = ("rejected: " + (res["front"] + res["backstop"])[0][:120]) if hit else (
                "passes" if res["passed"] else
                f"refused otherwise: {(res['diagnostics'] + res['source'])[:2]}")
            good &= record("baselines", f"{label} banlist", ok,
                           f"{what} (want {'banned' if b['banned'] else 'passes'}, at "
                           f"{[envelope.point_str(p) or 'default' for p in points]})",
                           time.time() - t0)
            if b.get("same_tokens_as"):
                a, c = canon_tokens(sv), canon_tokens(os.path.join(SVGOLF, b["same_tokens_as"]))
                good &= record("baselines", f"{label} same tokens", a is not None and a == c,
                               f"as {b['same_tokens_as']} (comments and whitespace aside)")
            good &= baseline_fourstate(t, task, label, sv, b)
            good &= baseline_postsynth(t, task, label, sv, b, args)
    return good


def step_baseline_proofs(tasks, expected, args):
    """Every baseline with its proof (tests/expected.json `lean`, relative to tests/<task>/) through check.py, decided
    2026-11-12: every design the site shows has a kernel-checked proof. A baseline the task's banlist rejects (`banned`)
    is checked with `--lift-banlist` (every stage, the proof's included, with only the task's operator banlist lifted)
    and must end at the pseudo-stage `lifted` with `lifted_ok`, the task banlist's own verdict `rejects`, and never
    `accepted`; any other baseline must be ACCEPTED. Either way: the comparator's axioms within the task's allowed set,
    the full post-synthesis check, and the score at the scoring point equal to tests/expected.json's. Each row says the
    wall seconds of the run and the CPU seconds of the solution stage against the task's limit."""
    good = True
    for t in tasks:
        task = task_json(t)
        tdir = os.path.join(SVGOLF, "tasks", t)
        allowed = set(task.get("allowed_axioms", ["propext", "Classical.choice", "Quot.sound"]))
        spoint = envelope.point_str(task["scoring"]["params"]) or "default"
        for stem, b in expected["tasks"][t]["baselines"].items():
            sv = design_path(t, "baselines", stem, b)
            label = rel(sv)
            lean = os.path.join(SVGOLF, "tests", t, b["lean"]) if b.get("lean") else None
            if lean is None or not os.path.isfile(lean):
                good &= record("baseline-proofs", label, False,
                               f"no proof file (tests/expected.json `lean` {b.get('lean')!r}): the site shows no design "
                               "without a kernel-checked proof")
                continue
            lifted = bool(b.get("banned"))
            res = run_check(tdir, sv, lean, args.check_extra + (["--lift-banlist"] if lifted else []),
                            ppa_flag=ppa_mode())
            st = res.get("stages") or {}
            sol = st.get("solution") or {}
            comp = (st.get("comparator") or {}).get("result") or {}
            axioms = sorted(comp.get("axioms") or [])
            if lifted:
                bl = res.get("banlist_lifted") or {}
                ok = (res.get("stage") == "lifted" and res.get("lifted_ok") is True and res.get("accepted") is False
                      and not res.get("errors") and bl.get("task_banlist") == "rejects" and res.get("_exit") == 0)
                what = ("proved with the banlist lifted, not an entry (the task's banlist rejects it: "
                        f"{(bl.get('task_findings') or ['?'])[0][:80]})" if ok else verdict(res))
            else:
                ok = bool(res.get("accepted")) and res.get("stage") == "done"
                what = verdict(res)
            ok = ok and comp.get("accepted") is True and bool(axioms) and set(axioms) <= allowed
            detail = (f"{what}; {rel(lean)}; axioms {axioms}; solution {sol.get('cpu_seconds')} CPU s of "
                      f"{sol.get('time_limit_s')} ({sol.get('seconds')} s wall)")
            good &= record("baseline-proofs", f"{label} with its proof", ok,
                           detail if ok else f"{detail}: {first_error(res)}", res["_seconds"])
            if not ok:
                continue
            ps = st.get("postsynth") or {}
            pok = (ps.get("mode") == "full" and ps.get("vectors") == ps.get("full_vectors") and ps.get("mismatches") == 0
                   and "light_vectors" not in ps)
            good &= record("baseline-proofs", f"{label} full postsynth", pok,
                           f"mode {ps.get('mode')}, {ps.get('vectors')} of {ps.get('full_vectors')} vectors, "
                           f"{ps.get('mismatches')} mismatches")
            want = (b.get("scores") or {}).get(spoint)
            if want:
                got = {k: res["score"][k] for k in SCORE_KEYS}
                same = same_score(got, want)
                good &= record("baseline-proofs", f"{label} check.py score {spoint}", same,
                               f"{got['area_mge'] / 1000:g} GE, depth {got['depth']}"
                               + ("" if same else f": {score_diff(got, want)}"))
    return good


def baseline_fourstate(t, task, label, sv, b):
    """The 4-state rules (score/fourstate.py, check.py's `fourstate` stage) at
    every point the baseline is scored or banlist-checked at: no legitimate
    design is refused (a banned-operator baseline included: the rules are
    independent of the banlist)."""
    pts = list(b.get("scores", {})) or b.get("banlist_points") or ["default"]
    canon, findings = envelope.gate(sv)
    if findings:
        return record("baselines", f"{label} fourstate", False, f"gate: {findings[:2]}")
    good = True
    with tempfile.TemporaryDirectory(prefix="svgolf-4s-") as tmp:
        c = os.path.join(tmp, os.path.basename(sv))
        with open(c, "w", newline="") as fh:
            fh.write(canon)
        for point in pts:
            t0 = time.time()
            res = fourstate.check([c], task["top"], parse_point(point))
            good &= record("baselines", f"{label} fourstate {point}", res["passed"],
                           "passes" if res["passed"] else
                           str((res["findings"] + res["diagnostics"])[:2])[:300],
                           time.time() - t0)
    return good


def baseline_postsynth(t, task, label, sv, b, args, step="baselines"):
    """The postsynth check of a baseline: it must pass. At `postsynth_points`
    when expected.json gives them (`[]` skips, with the reason in
    `postsynth_why`); otherwise at the task's scoring point when the baseline
    is scored there (else its first scored point), and with --full at every
    scored point."""
    scored = list(b.get("scores", {}))
    spoint = envelope.point_str(task["scoring"]["params"]) or "default"
    if "postsynth_points" in b:
        points = b["postsynth_points"]
    elif args.full:
        points = scored
    else:
        points = [spoint] if spoint in scored else scored[:1]
    if not points:
        return record(step, f"{label} postsynth", True,
                      "not run: " + b.get("postsynth_why", "no scored point"))
    good = True
    tdir = os.path.join(SVGOLF, "tasks", t)
    for point in points:
        t0 = time.time()
        with tempfile.TemporaryDirectory(prefix="svgolf-ps-") as work:
            try:
                r = postsynth.check_design(tdir, sv, work, point=parse_point(point), mode="full")
                ok, what = True, (f"ls-sv and the netlist agree on {r['vectors']} vectors "
                                  f"(ls-sv {r['t_lssv_s']}s, {r['lssv_ms_per_vector']} ms/vector)")
                f = r.get("functional")
                if f is not None:
                    # every baseline and goalpost is a validated design: the advisory oracle
                    # must agree with it on every vector too
                    fok = (f["mismatches"] == 0 and f["checked"] == r["vectors"]
                           and "unchecked" not in f)
                    ok &= fok
                    what += (f"; the task's oracle agrees on {f['checked']} vectors" if fok
                             else f"; the task's oracle DISAGREES: {f}")
            except postsynth.Reject as e:
                ok, what = False, e.msg.splitlines()[0]
            except (postsynth.InfraError, envelope.InfraError, envelope.Refused,
                    score.ScoreError) as e:
                ok, what = False, f"{type(e).__name__}: {str(e).splitlines()[0][:200]}"
        good &= record(step, f"{label} postsynth {point}", ok, what, time.time() - t0)
    return good


# ---------------------------------------------------------------------------
# ppa: the extra sky130 columns of the designs no real check.py result carried (WP-X3)
# ---------------------------------------------------------------------------

def step_ppa(tasks, expected, args):
    """Every design of score/tests/ppa/designs.json (the references, the baselines, the banned-operator probes, the
    draft goalpost) that the `references` step did not already see in a real check.py result, and of idioms.json (the
    designs whose netlists carry the dead public-named wires of techmapped cells: run-time bit select, variable shift,
    case mux, constant table, divider ...): the pinned flow's scored netlist of the design at its scoring point, weighed
    by check.py's own `ppa_block` (the function its `ppa` stage runs on the netlist the score stage kept), equal to the
    goldens of score/tests/ppa/expected_ppa.json / expected_idioms.json. The designs are scored without the banlist, as
    in tests/expected.json (`banned`)."""
    state = ppa_state()[0]
    if state == "invalid":
        return record("ppa", "pinned liberty", False,
                      f"{ppa_state()[1]} is not the pinned file: {ppa_state()[2]}")
    if state == "absent":
        return record("ppa", "sky130 PPA columns", True, ppa_skip_note())
    by_src, designs, gold = ppa_gold()
    pins = ppa.Pins()
    good = True
    for gfile, g in gold["identity"]:
        good &= record("ppa", f"score/tests/ppa/{gfile} is for the pinned inputs",
                       g["liberty_sha256"] == pins.lib["sha256"] and g["ppa_version"] == pins.version,
                       f"{pins.version}, liberty {pins.lib['sha256'][:12]}")
    mpins = ppa.MappedPins(pins)
    mg = gold["mapped_file"]
    live = {"ppa_mapped_version": mpins.version, "liberty_sha256": pins.lib["sha256"],
            "ppa_mapped_script_sha256": mpins.script_sha256, "yosys_version": score.yosys_version(score.yosys_bin()),
            "abc_version": ppa.abc_version(score.yosys_bin())}
    stale = [k for k, v in live.items() if mg.get(k) != v]
    good &= record("ppa", "score/tests/ppa/expected_ppa_mapped.json is for the pinned inputs (flow A1')", not stale,
                   f"{mpins.version}, script {mpins.script_sha256[:12]}, liberty {pins.lib['sha256'][:12]}" if not stale
                   else "recorded under another " + ", ".join(stale) + ": a changed script, pins file or tool build changes the "
                   "mapped numbers; bump `ppa_mapped_version` and re-record with `ppa_validate.py table --designs "
                   "designs.json,idioms.json --mapped-expected-out score/tests/ppa/expected_ppa_mapped.json`")
    for d in designs:
        # the netlist-reader idioms (task "idioms") belong to no task: they run with the step, whatever `--only` says
        if (d["task"] not in tasks and d["task"] != "idioms") or d["name"] in PPA_REFERENCE_NAMES:
            continue
        t0 = time.time()
        sv = os.path.join(SVGOLF, d["src"])
        dtask = task_json(d["task"]) if d["task"] != "idioms" else None     # its input drive (idioms: the default)
        with tempfile.TemporaryDirectory(prefix="svgolf-ppa-") as work:
            net, il = os.path.join(work, "netlist.v"), os.path.join(work, "canon.il")
            try:
                sres = score.score([sv], d["top"], d["params"], netlist_out=net, rtlil_out=il)
                block = checkpy().ppa_block(net, sres, "require", task=dtask)
                mapped = checkpy().ppa_mapped_block(il, d["top"], net, "require", None, sres["rtlil_sha256"])
            except (score.ScoreError, RuntimeError) as e:
                good &= record("ppa", d["name"], False, f"{type(e).__name__}: {str(e).splitlines()[0][:200]}",
                               time.time() - t0)
                continue
        probs = ppa_block_problems(block, sres, dtask) or ppa_vs_gold(block, sres, gold["designs"][d["name"]])
        mprobs = (ppa_mapped_block_problems(mapped, sres["rtlil_sha256"])
                  or ppa_mapped_vs_gold(mapped, gold["mapped"][d["name"]]))
        good &= record("ppa", d["name"], not probs and not mprobs,
                       (f"{sres['area_ge']} GE / depth {sres['depth']} -> {block['area_um2_sky130']} um^2, "
                        f"{block['delay_ps_sky130']} ps (= the golden); mapped A1' {mapped['area_um2_sky130_mapped_v1']} um^2, "
                        f"{mapped['mapped_delay_sky130_v1']} ps, {mapped['mapped_cells_sky130_v1']} cells (= the golden)")
                       if not probs and not mprobs else "; ".join(probs + mprobs),
                       time.time() - t0)
    return good


# ---------------------------------------------------------------------------
# validation (simulation)
# ---------------------------------------------------------------------------

def fdivp_validation(full):
    """The validation rows of `fdivp` (tests/fdivp/validate/validate.py, README there): the four oracles tied
    together and the reference simulated against the C++ oracle (exhaustive on small formats, corner-rich samples on
    the large ones); each baseline at the formats it is right at; each attack and the `const_nan` negative must be
    wrong at SOME listed format (`--bad`), and `dsh_wrap64`/`ew_narrow` right at the scoring point (their point); the
    Newton and SRT references by the same plan, and each of their attacks wrong somewhere ((4, 6) in the quick plan)."""
    V = [PY, "tests/fdivp/validate/validate.py"]
    small = ["2,2", "3,4", "4,6", "7,3", "2,8"]
    rows = [("validate.py --plan " + ("full (66 formats exhaustive, 2^32 pairs at (5,11) and (8,8); hours)" if full
                                      else "quick (oracles; 12 small formats exhaustive; 4 large sampled)"),
             V + ["--plan", "full" if full else "quick"], ["tasks/fdivp/reference/fdivp.sv"])]
    # the proved baseline D2, and the test material of tests/fdivp/unproved/ (no proof: shown nowhere on the site)
    for d, where in (("fdivp_d1", "unproved"), ("fdivp_d2", "baselines")):
        rows.append((f"validate.py {d} ({'proved baseline' if where == 'baselines' else 'test material'}: small "
                     "formats exhaustive, (5, 11) sampled)",
                     V + ["--design", f"tests/fdivp/{where}/{d}.sv", "--formats"] + small + ["5,11", "--samples",
                                                                                          "300000" if full else "60000"],
                     [f"tests/fdivp/{where}/{d}.sv"]))
    rows.append(("validate.py flat_binary16 (test material: right at (5, 11) only)",
                 V + ["--design", "tests/fdivp/unproved/flat_binary16.sv", "--formats", "5,11", "--samples",
                      "1000000" if full else "200000"], ["tests/fdivp/unproved/flat_binary16.sv"]))
    for k in ("div_op", "rm_pin", "status_flag", "wide_q"):
        rows.append((f"validate.py {k} (negative: right function, refused by the banlist or the interface)",
                     V + ["--design", f"tests/fdivp/negative/{k}.sv", "--formats"] + small, []))
    rows.append(("validate.py --bad const_nan (negative: wrong somewhere)",
                 V + ["--design", "tests/fdivp/negative/const_nan.sv", "--bad", "--formats", "2,2", "3,4", "4,6"], []))
    for k in ("inc_tie_odd", "dsh_wrap64", "ew_narrow", "zero_by_zero_inf", "rr_sticky_dropped", "ftz", "ovf_late",
              "dsh_sticky_short"):
        rows.append((f"validate.py --bad {k} (attack: wrong somewhere)",
                     V + ["--design", f"tests/fdivp/attacks/{k}.sv", "--bad", "--formats"] + small
                     + ["5,5", "8,2"], []))
    for k in ("dsh_wrap64", "ew_narrow"):
        rows.append((f"validate.py {k} at the scoring point (5, 11): right there, wrong elsewhere",
                     V + ["--design", f"tests/fdivp/attacks/{k}.sv", "--formats", "5,11", "--samples", "300000"], []))
    # the Newton reference, by the reference's plan; its attacks are all wrong at (4, 6), the one format of the quick plan
    # (newton_no_ge2 and newton_rnz_no2mb are wrong only at P = 6 among W = 2, P = 2..12)
    rows.append(("validate.py --plan " + ("full" if full else "quick") + " --design fdivp_newton.sv (the Newton reference)",
                 V + ["--plan", "full" if full else "quick", "--design", "tasks/fdivp/reference/fdivp_newton.sv"],
                 ["tasks/fdivp/reference/fdivp_newton.sv"]))
    for k in ("newton_f_minus2", "newton_ge1_const", "newton_ni_minus1", "newton_no_ge2", "newton_r0_off",
              "newton_rnz_no2mb", "newton_rnz_nomb"):
        rows.append((f"validate.py --bad {k} (attack on the Newton reference: wrong somewhere)",
                     V + ["--design", f"tests/fdivp/attacks/{k}.sv", "--bad", "--formats"]
                     + (small + ["5,5", "8,2", "2,6", "3,6"] if full else ["4,6"]), []))
    # the SRT reference, by the reference's plan; its attacks are all wrong at (4, 6) too (the three table attacks are
    # right below P = 5: the bad cells are not reached)
    rows.append(("validate.py --plan " + ("full" if full else "quick") + " --design fdivp_srt.sv (the SRT reference)",
                 V + ["--plan", "full" if full else "quick", "--design", "tasks/fdivp/reference/fdivp_srt.sv"],
                 ["tasks/fdivp/reference/fdivp_srt.sv"]))
    for k in ("srt_qds_t2_d0", "srt_qds_t1_d0", "srt_qds_tm_d7", "srt_no_corr", "srt_drop_carry", "srt_no_cin",
              "srt_sticky_sign", "srt_stages_m1", "srt_otfc_um", "srt_otfc_digit"):
        rows.append((f"validate.py --bad {k} (attack on the SRT reference: wrong somewhere)",
                     V + ["--design", f"tests/fdivp/attacks/{k}.sv", "--bad", "--formats"]
                     + (small + ["5,5", "8,2", "2,6", "3,6"] if full else ["4,6"]), []))
    return rows


def VALIDATION(full, work):
    """task -> [(label, command, designs it validates (paths relative to svgolf/))].
    Measured quick runtimes (2026-10-28): add ~50 s, mul ~10 s; aes_sbox
    (2026-10-30): ~25 s (seven Verilator builds)."""
    wrap = ["--lean-wrap", " ".join(WRAP)] if WRAP else []
    add_designs = ["tasks/add/reference/add_n.sv", "tests/add/baselines/add_n_sklansky.sv",
                   "tests/add/baselines/add_n_kogge_stone.sv", "tests/add/baselines/cmp_carry.sv",
                   "tests/add/negative/plus.sv", "tasks/add/reference/add_proc.sv",
                   "tasks/add/reference/add_proc_m.sv", "tasks/add/reference/add_mux.sv"]
    aes_good = ["tasks/aes_sbox/reference/sbox_bp.sv", "tasks/aes_sbox/reference/sbox_table.sv",
                "tests/aes_sbox/baselines/sbox_bp_d16.sv"]
    aes_bad = [f"tests/aes_sbox/negative/{n}.sv" for n in
               ("no_constant", "one_entry", "reversed_bits", "inverse_sbox")]
    # the proved parametric baselines (every width), and the one-width generated netlists of tests/clmul/unproved/
    # (test material: no proof, shown nowhere on the site), each at its own width
    clmul_baselines = ["clmul_tree", "kara_lv", "clmul_k1"]
    clmul_onewidth = [("school_tree_8", 8), ("school_tree_16", 16), ("school_tree_32", 32),
                      ("kara_b4_8", 8), ("kara_b4_16", 16), ("kara_b4_32", 32), ("kara_b2_16", 16),
                      ("kara_b8_16", 16), ("kara_full_16", 16)]
    clmul_styles = sorted(os.path.basename(f)[:-3] for f in
                          glob.glob(os.path.join(SVGOLF, "tests", "clmul", "attacks", "*.sv")))
    v = {
        "add": [
            # quick: Verilator + run2 (both schedules) exhaustive at N = 1..3, sampled at 8, 16;
            # full: the documented plan (N = 1..5 exhaustive, 9 sampled widths up to 64; ~1 h)
            ("validate.py: Verilator + ls-sv run2 vs a + b + cin (every design, mutants caught)",
             [PY, "tests/add/validate/validate.py"] + wrap
             + ([] if full else ["--widths", "1,2,3,8,16", "--samples", "20"]),
             add_designs + [f"tests/add/negative/{n}.sv" for n in
                            ("no_cin", "cout_off", "carry_bug", "only_n16")]),
            ("postsynth.py: the scored netlists in Verilator",
             [PY, "tests/add/validate/postsynth.py"]
             + ([] if full else ["--widths", "16,32", "--vectors", "500"]),
             add_designs),
        ] + ([("verilator.py: Verilator, 200 000 random vectors at N = 5, 16, 33, 64",
               [PY, "tests/add/validate/verilator.py"], add_designs[:3])] if full else []),
        "mul": [
            ("sim.py mul_n (reference): " + ("full plan" if full else "quick plan"),
             [PY, "tests/mul/validate/sim.py", "tasks/mul/reference/mul_n.sv", "--plan",
              "full" if full else "quick"], ["tasks/mul/reference/mul_n.sv"]),
            ("sim.py mul_tree (reference): " + ("full plan" if full else "quick plan"),
             [PY, "tests/mul/validate/sim.py", "tasks/mul/reference/mul_tree.sv", "--plan",
              "full" if full else "quick"], ["tasks/mul/reference/mul_tree.sv"]),
            ("sim.py mul_wallace (reference): " + ("full plan" if full else "quick plan"),
             [PY, "tests/mul/validate/sim.py", "tasks/mul/reference/mul_wallace.sv", "--plan",
              "full" if full else "quick"], ["tasks/mul/reference/mul_wallace.sv"]),
            ("sim.py mul_tree_h (reference): " + ("full plan" if full else "quick plan"),
             [PY, "tests/mul/validate/sim.py", "tasks/mul/reference/mul_tree_h.sv", "--plan",
              "full" if full else "quick"], ["tasks/mul/reference/mul_tree_h.sv"]),
            ("sim.py yosys_mul: " + ("full plan" if full else "quick plan"),
             [PY, "tests/mul/validate/sim.py", "tests/mul/baselines/yosys_mul.sv", "--plan",
              "full" if full else "quick"], ["tests/mul/baselines/yosys_mul.sv"]),
            ("sim.py dadda_rc (proved baseline, every N): " + ("full plan" if full else "quick plan"),
             [PY, "tests/mul/validate/sim.py", "tests/mul/baselines/dadda_rc.sv", "--plan",
              "full" if full else "quick"], ["tests/mul/baselines/dadda_rc.sv"]),
        ] + [(f"sim.py dadda_{k}_{n} at N = {n} (test material, tests/mul/unproved/)",
              [PY, "tests/mul/validate/sim.py", f"tests/mul/unproved/dadda_{k}_{n}.sv",
               "--width", str(n)] + ([] if full or n <= 8 else ["--vectors", "2000"]),
              [f"tests/mul/unproved/dadda_{k}_{n}.sv"])
             for k in ("rc", "ks") for n in (8, 16, 32)],
        "aes_sbox": [
            # quick = full: the input space is 256 values, every step is exhaustive and takes seconds
            ("validate.py: oracle = FIPS 197 Table 4 (NIST PDF), anchors, AES-128 vs OpenSSL, both "
             "Boyar-Peralta netlists gate for gate, Verilator on all 256 inputs",
             [PY, "tests/aes_sbox/validate/validate.py", "--good"] + aes_good + ["--bad"] + aes_bad,
             aes_good),
        ],
        "clmul": [
            ("validate.py: oracle = Kronecker substitution, FIPS 197 anchors, the Lean spec = the oracle on "
             "every pair at N <= 7",
             [PY, "tests/clmul/validate/validate.py"] + wrap, []),
            ("sim.py clmul_n (reference): " + ("full plan" if full else "quick plan"),
             [PY, "tests/clmul/validate/sim.py", "tasks/clmul/reference/clmul_n.sv", "--plan",
              "full" if full else "quick"], ["tasks/clmul/reference/clmul_n.sv"]),
        ] + [(f"sim.py {k} (proved baseline): " + ("full plan" if full else "quick plan"),
              [PY, "tests/clmul/validate/sim.py", f"tests/clmul/baselines/{k}.sv", "--plan",
               "full" if full else "quick"], [f"tests/clmul/baselines/{k}.sv"])
             for k in clmul_baselines] + [
            (f"sim.py {k} at N = {n} (test material, tests/clmul/unproved/)",
             [PY, "tests/clmul/validate/sim.py", f"tests/clmul/unproved/{k}.sv", "--width", str(n)]
             + ([] if full or n <= 8 else ["--vectors", "2000"]),
             [f"tests/clmul/unproved/{k}.sv"])
            for k, n in clmul_onewidth] + [
            (f"sim.py {k} (a correct design the checker refuses by the banlist or the interface)",
             [PY, "tests/clmul/validate/sim.py", f"tests/clmul/negative/{k}.sv", "--plan", "quick"],
             [f"tests/clmul/negative/{k}.sv"])
            for k in ("plus_xor", "kronecker_mul", "wide_out")] + [
            (f"sim.py --bad {k} (a wrong design: some point must show a mismatch)",
             [PY, "tests/clmul/validate/sim.py", f"tests/clmul/negative/{k}.sv", "--plan", "quick", "--bad"],
             [f"tests/clmul/negative/{k}.sv"])
            for k in ("top_shift", "drop_top", "or_accumulate", "reversed_p", "only_n16")] + [
            (f"sim.py {k} (a real-world style, correct for every N: tests/clmul/attacks)",
             [PY, "tests/clmul/validate/sim.py", f"tests/clmul/attacks/{k}.sv", "--plan", "quick"],
             [f"tests/clmul/attacks/{k}.sv"])
            for k in clmul_styles],
        "fdivp": fdivp_validation(full),
        "arbiter": [
            # Icarus on tb.sv, the statement read per snapshot plus the silicon Moore check, at N = 1, 2, 3, 4, 5, 8,
            # four stimulus modes, each design from a 0/1 power-up state (sim.py `powerup`, 2026-11-07; a state bit
            # left without a 0/1 value is an error, the review's F1): the goalpost and the two other correct designs
            # pass, every attack fails on its clause (A17 passes here by design: a reset comes before its bomb;
            # check.py's postsynth rejects it), and the harness's self-test selftest/alias_ptr.sv fails on G3 with
            # the self-check XK silent. Quick: 4000 cycles per run (about 60 s); full: 20000.
            ("sim.py: the goalpost, designs/, the 17 attacks and the harness self-test (Icarus, tb.sv)",
             [PY, "tests/arbiter/sim.py", "--cycles", "20000" if full else "4000"],
             ["tasks/arbiter/reference/rr_mask.sv", "tests/arbiter/designs/rotate.sv",
              "tests/arbiter/designs/arbiter_ot.sv"]),
        ],
    }
    return v


def step_validate(tasks, expected, args):
    good = True
    work = tempfile.mkdtemp(prefix="svgolf-validate-")
    try:
        v = VALIDATION(args.full, work)
        for t in tasks:
            covered = set()
            for label, cmd, designs in v.get(t, []):
                covered |= set(designs)
                t0 = time.time()
                proc = subprocess.run(cmd, cwd=SVGOLF, capture_output=True, text=True)
                out = (proc.stdout + proc.stderr).strip().splitlines()
                good &= record("validate", f"{t}: {label}", proc.returncode == 0,
                               (out[-1][:160] if out else "") if proc.returncode == 0
                               else "\n".join(out[-25:]), time.time() - t0)
            if t not in v:
                continue   # no validation script (`_example`: `assign y = a & b;`, proved)
            # every reference / draft goalpost / baseline of a task with validation
            # scripts is simulated (or token-identical to one that is)
            e = expected["tasks"][t]
            need = ([rel(design_path(t, "references", s, x)) for s, x in e["references"].items()
                     if not x.get("same_design_as")]
                    + [rel(design_path(t, "baselines", s, x)) for s, x in e["baselines"].items()
                       if not x.get("same_tokens_as")])
            missing = [d for d in need if d not in covered]
            good &= record("validate", f"{t}: coverage", not missing,
                           "every reference and baseline simulated" if not missing
                           else f"not simulated by any validation step: {missing}")
    finally:
        shutil.rmtree(work, ignore_errors=True)
    return good


# ---------------------------------------------------------------------------
# attacks on the checker
# ---------------------------------------------------------------------------

ATTACKS = {
    "wrong_statement": ("""import Submission.Design
namespace Submission
theorem solution : True := trivial
end Submission
""", "comparator"),
    "extra_axiom": ("""import Submission.Design
namespace Submission
axiom cheat : Goal
theorem solution : Goal := cheat
end Submission
""", "comparator"),
    "env_hack_top": ("""import Submission.Design
import Lean
open Lean Elab Command

def hackDecl : Declaration :=
  .thmDecl { name := `Submission.solution, levelParams := [],
             type := mkConst `Submission.Goal, value := mkConst ``trivial }

#eval show CommandElabM Unit from do
  match (← getEnv).addDeclCore 0 0 hackDecl none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "unexpected"
""", "comparator"),
    "env_hack_dep": ("""import Submission.Design
import Lean
open Lean Elab Command

def hackDecl : Declaration :=
  .thmDecl { name := `Submission.helper, levelParams := [],
             type := mkConst `Submission.Goal, value := mkConst ``trivial }

#eval show CommandElabM Unit from do
  match (← getEnv).addDeclCore 0 0 hackDecl none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "unexpected"

namespace Submission
theorem solution : Goal := helper
end Submission
""", "leanchecker"),
    "bad_import": ("""import Submission.Design
import Examples.«system-verilog».ripple_add.proof
namespace Submission
theorem solution : True := trivial
end Submission
""", "imports"),
    "bad_import_lookalike": ("""import Submission.Design
import LeanModels.Sv.CombLib
import Mathlib2.Tactic
namespace Submission
theorem solution : True := trivial
end Submission
""", "imports"),
    "bad_import_python": ("""import Submission.Design
import LeanModels.Python.Semantics
namespace Submission
theorem solution : True := trivial
end Submission
""", "imports"),
    "no_design_import": ("""import SvGolf.Task
theorem solution : True := trivial
""", "imports"),
}

PARAM_W_SV = """module band #(parameter int W = 4) (
  input  logic [W-1:0] a,
  input  logic [W-1:0] b,
  output logic [W-1:0] y
);
  assign y = a & b;
endmodule
"""

NARROW_PARAM_SV = """module band #(parameter bit [3:0] N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  assign y = a & b;
endmodule
"""

# The source-gate fixtures that are `band` designs (all refused at `source`).
GATE_FIXTURES = ["ifdef_synth.sv", "ifdef_yosys.sv", "translate_off2.sv", "full_case.sv",
                 "attr_full_case.sv", "unique_case.sv", "priority_case.sv", "xz_case_items.sv",
                 "casez_x_item.sv",
                 # host access (P-NO-HOST-ACCESS): file, process, environment, dump and DPI
                 "host_readmemh.sv", "host_memfile_write.sv", "host_fopen.sv", "host_fread.sv",
                 "host_system.sv", "host_plusargs.sv", "host_dump.sv", "host_dump_comb.sv",
                 "host_dpi_import.sv", "host_dpi_export.sv", "host_other_files.sv",
                 "host_escaped.sv", "host_escaped_shadow.sv", "host_dead_code.sv", "host_macro.sv"]
# The positive twins: `band` designs that NAME the refused constructs (in comments, in string
# literals, in an identifier that merely contains a `$`) and must pass the whole flow up to the
# proof (`check.py --unproved`: nothing in them is a use). A gate that refused prose would break
# every design with a comment about `$readmemh`.
GATE_OK_FIXTURES = ["ok_host_comments.sv", "ok_host_words.sv"]
GATE_DIR = os.path.join(SVGOLF, "score", "tests", "gate")
# WP-B: the `_example` reference proof with Mathlib tactics (accepted), and the attacks derived from it.
MATHLIB_FIXTURE = os.path.join(HERE, "imports", "mathlib_band.lean")
# every reference proved with the sv_comb tactics: all of them are accepted under `import Mathlib.Tactic` with the
# proof otherwise unchanged (the tactics' own `simp` runs with Lean core's simp set: `sv_simp`,
# LeanModels/Sv/CombCoreSimp.lean; before gate M (2026-11-01) it needed `sv_core_simp`, SvGolf/CoreSimp.lean)
TACTIC_REFERENCES = [("_example", "band_tactics"), ("add", "add_n"), ("add", "add_proc"), ("add", "add_proc_m"),
                     ("mul", "mul_n"),
                     ("mul", "mul_wallace"),
                     ("mul", "mul_tree_h"), ("mul", "mul_tree"), ("aes_sbox", "sbox_bp"), ("clmul", "clmul_n"),
                     ("fdivp", "fdivp")]
# The `host_env_salt` attack's probe (WP-S): throws, so the file does not compile, if the checker's
# secrets are visible to the Lean process by name (`IO.getEnv`) or by value (the whole environment,
# `Std.Internal.UV.System.osEnviron`). Accepted = invisible.
SALT_PROBE = """
#eval show IO Unit from do
  for v in ["SVGOLF_POSTSYNTH_SALT", "CLAUDE_CODE_MESSAGING_TOKEN", "GITHUB_TOKEN", "SVGOLF_LEAN_WRAP"] do
    if (← IO.getEnv v).isSome then throw (IO.userError s!"SECRET VISIBLE by name: {v}")
  for (k, v) in (← Std.Internal.UV.System.osEnviron) do
    if k.startsWith "SVGOLF_" || (v.splitOn "wps-").length > 1 then
      throw (IO.userError s!"SECRET VISIBLE in the environment dump: {k}")
"""
NATIVE_MARKER = "/-- **The reference solution**"
NATIVE_USE = "  have _hp := pow_facts N\n"

# A FORGED `bv_decide` axiom (WP-BV): exactly the name and type shape the tactic generates, over a satisfiable
# formula and an empty certificate, so `verifyBVExpr E C` evaluates to `false`. check.py never passes `--bv-decide`
# (bv_decide is not supported, decided 2026-11-01), so the comparator rejects it by POLICY; the groundwork row
# `bv_decide_groundwork_forged` runs the same file through the wrapper that forces the dormant support on, and the
# comparator's re-check refuses it by EVALUATION.
BV_AXIOM = """
open Std.Tactic.BVDecide in
def forgedE : BVLogicalExpr := .const true
def forgedC : String := ""
open Std.Tactic.BVDecide in
/-- An axiom with exactly the name and type shape `bv_decide` generates, over a false certificate. -/
axiom solution._native.bv_decide.ax_1 : Reflect.verifyBVExpr forgedE forgedC = true

/-- **The reference solution**"""
# A fixed-size fact closed by `bv_decide`, used by the reference proof: REFUSED by default (`bv_decide_subgoal_*`: the
# sandbox stops the solver, or the comparator rejects the axiom by policy), ACCEPTED with the dormant support forced on
# (`bv_decide_groundwork_accepted`: the comparator re-verifies its certificate)
BV_HELPER = """/-- A fixed-size fact closed by `bv_decide`, used by the proof below. -/
theorem bv_helper : ∀ a b : BitVec 16, (a &&& b) + (a ||| b) = a + b := by
  intro a b
  bv_decide

/-- **The reference solution**"""
# The `slow_proof` attack (item 9 of the from-scratch study): a step that outlasts the test's limit, before the reference
# proof's theorem. `sleep` waits and computes nothing, so it never reaches the CPU limit (decided 2026-11-05: the limit
# counts CPU seconds) and the run is stopped by the wall-clock BACKSTOP (check.py's SOLUTION_WALL_FACTOR x the limit),
# after the declarations above it finished in about 2 s.
SLOW_STEP = """/-- A step that takes longer than the test's limit: `sleep` waits, nothing is computed. -/
theorem slow_step : True := by
  sleep 600000
  trivial

/-- **The reference solution**"""
# The `cpu_proof` attack: the same place, a step that COMPUTES past the CPU limit (`#eval` of a loop of 10^12 steps),
# stopped by the CPU limit long before the backstop.
CPU_STEP = """/-- A step that computes past the test's CPU limit: `#eval` runs a loop of 10^12 steps. -/
def burn : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => burn n (acc + 1)

#eval burn 1000000000000 0

/-- **The reference solution**"""
SLOW_LIMIT_S = 10
# the declaration of `_example`'s first reference proof just above the slow step: the last one that finishes
SLOW_LAST = "Submission.band_interface"


def step_attacks(args):
    """The checker's defenses, on `_example` with its first reference:

      wrong_statement   proves `True` instead of the goal          -> comparator
      extra_axiom       an `axiom` of the goal                     -> comparator
      bv_decide_shaped  a valid proof that also depends on a hand-
                        declared axiom with bv_decide's name and
                        type shape (`verifyBVExpr e c = true`):
                        bv_decide is not supported, the comparator
                        rejects every such axiom BY POLICY, with
                        the message that names it (WP-BV G3)        -> comparator
      bv_decide_subgoal_sandbox / _off
                        the reference proof plus a fixed-size lemma
                        closed by a real `bv_decide`, which the proof
                        uses. Sandbox ON: the solver cannot start, the
                        compile fails ("operation not permitted") and
                        the `solution` rejection carries the HINT
                        (`_sandbox`, only where the sandbox works).
                        Sandbox OFF: the compile succeeds and the
                        comparator rejects the axiom, naming the policy
                        (`_off`)                                    -> solution / comparator
      bv_decide_groundwork_accepted / _forged
                        (DORMANT groundwork, through tests/checker/check_bv_enabled.py, which forces
                        check.py's BV_DECIDE_SUPPORTED on in its own process) the same two files:
                        the real subgoal is ACCEPTED, its axiom re-verified by the comparator; the
                        forged axiom is rejected by EVALUATION ("does not verify")  -> done / comparator
      implemented_by    a valid proof plus an `implemented_by`     -> comparator
      slow_proof        the reference proof with a step that sleeps
                        before `solution`, under a 10 s CPU limit
                        (`--time-limit 10`): sleeping uses no CPU, so
                        the WALL-CLOCK BACKSTOP (50 s) stops it, with
                        its few CPU seconds reported apart, and the
                        rejection says where the time went, naming
                        the declaration above the step as the last
                        one that finished (item 9 of the from-scratch
                        study: Lean's stdout is a pseudo-terminal and
                        `trace.Kernel` is on)                      -> solution
      cpu_proof         the same place, a step that computes (`#eval`
                        of a 10^12-step loop): stopped by the 10 s CPU
                        limit (`stopped_by: cpu`), long before the
                        backstop                                   -> solution
      env_hack_top      adds `solution : Goal := trivial` with the
                        kernel check switched off                  -> comparator
      env_hack_dep      the same for a lemma `helper`, and a real
                        `theorem solution : Goal := helper`        -> leanchecker
      bad_import        imports `Examples.*`                       -> imports
      bad_import_lookalike imports `Mathlib2.Tactic` (next to an allowed
                        sv_comb library module; Mathlib itself is
                        allowed since WP-B)                        -> imports
      bad_import_python imports `LeanModels.Python.*`              -> imports
      no_design_import  does not import `Submission.Design`        -> imports
      mathlib_band      ACCEPTED: the `_example` reference proof with
                        Mathlib tactics (`ring`, `linarith`, `positivity`,
                        `norm_num`) in its arithmetic, tests/imports/
                        mathlib_band.lean                          -> done
      mathlib_lookalike the same file importing `Mathlib2.Tactic.Ring` -> imports
      mathlib_tactics_<ref> ACCEPTED, for every tactic-proved reference (band_tactics, add_n, add_proc, add_proc_m, mul_n,
                        mul_wallace, mul_tree_h, mul_tree, sbox_bp, clmul_n, fdivp): the reference proof
                        unchanged but for `import Mathlib.Tactic` (the tactics' own
                        `simp` ignores Mathlib's simp lemmas: `sv_simp`; no
                        `sv_core_simp` line is needed);
                        `--time-limit 900`: the proof is tested, not the machine's
                        load                                           -> done
      mathlib_glued_lookalike
                        `import SvGolf.Comb/-c-/import Mathlib2.Tactic.Ring`: a block
                        comment between two imports on one line (the checker used to
                        splice them into one token and never see the second) -> imports
      host_env_salt     ACCEPTED: the reference proof plus an `#eval` that throws when the
                        checker's secrets are visible to the Lean file (the competition salt
                        `SVGOLF_POSTSYNTH_SALT`, tokens, the whole environment is listed): the
                        child's environment is an allowlist (WP-S)    -> done
      mathlib_plant_free / mathlib_plant_importing
                        a solution whose build creates a file `*.olean` inside Mathlib's
                        build directory (the package-free reference proof, and the
                        Mathlib fixture): the integrity tripwire watches the Lean
                        search path for EVERY solution -> integrity. The runner removes
                        the file afterwards (it is a name no module has)
      mathlib_native_decide / mathlib_decide_native
                        the same file with a helper lemma closed by
                        native evaluation (`native_decide`,
                        `decide +native`) that the proof uses; the
                        generated axiom `native_helper._native.*` is
                        in the walked closure                      -> comparator
      param_name        the design's parameter is `W`, not `N`     -> extract
      narrow_param      `parameter bit [3:0] N`: Yosys would score
                        N = 16 as N = 0 (a 2-bit AND); the port
                        check refuses it first (at N = 16 its ports
                        are 2 bits wide, the task's 16); the probe
                        cross-check at the scoring point (`design`)
                        is the second line                         -> extract
      gate:<fixture>    each design in score/tests/gate that the
                        source gate refuses (`ifdef SYNTHESIS`,
                        `translate_off`, `unique case`, x/z literal
                        digits, `$readmemh`/`$fopen`/`$system`/DPI,
                        ...), with the reference proof             -> source
      gate-ok:<fixture> each ok_host_* design (the refused names only
                        in comments, strings, a `$`-containing
                        identifier), through --unproved: no source
                        finding, every check that needs no proof
                        passes                                     -> unproved
    """
    tdir = os.path.join(SVGOLF, "tasks", "_example")
    task = task_json("_example")
    ref_sv = os.path.join(tdir, task["references"][0]["sv"])
    ref_lean = os.path.join(tdir, task["references"][0]["lean"])
    extra = args.check_extra + ["--no-score"]
    good = True
    with tempfile.TemporaryDirectory(prefix="svgolf-attacks-") as tmp:
        cases = dict(ATTACKS)
        with open(ref_lean) as fh:
            proof = fh.read()
        cases["implemented_by"] = (proof.replace("end Submission", """
def fastId (n : Nat) : Nat := n
@[implemented_by fastId] def slowId (n : Nat) : Nat := n

end Submission"""), "comparator")
        slow = proof.replace("/-- **The reference solution**", SLOW_STEP, 1)
        if slow == proof or f"theorem {SLOW_LAST.split('.')[-1]} " not in proof:
            return record("attacks", "slow_proof", False, "the reference proof changed shape; update the attack")
        cases["slow_proof"] = (slow, "solution")
        cases["cpu_proof"] = (proof.replace("/-- **The reference solution**", CPU_STEP, 1), "solution")
        bv = proof.replace("import Submission.Design", "import Submission.Design\n"
                           "import Std.Tactic.BVDecide")
        bvok = bv.replace("/-- **The reference solution**", BV_HELPER)
        bvok = bvok.replace("theorem solution : Goal := by\n",
                            "theorem solution : Goal := by\n"
                            "  have _hbv := bv_helper\n")
        bv = bv.replace("/-- **The reference solution**", BV_AXIOM)
        bv = bv.replace("theorem solution : Goal := by\n",
                        "theorem solution : Goal := by\n"
                        "  have _h := solution._native.bv_decide.ax_1\n")
        if "ax_1\n  intro" not in bv or "_hbv := bv_helper\n  intro" not in bvok:
            return record("attacks", "bv_decide_shaped", False,
                          "the reference proof changed shape; update the attack")
        cases["bv_decide_shaped"] = (bv, "comparator")
        cases["bv_decide_subgoal_off"] = (bvok, "comparator")
        if sandbox_state()[0]:
            cases["bv_decide_subgoal_sandbox"] = (bvok, "solution")
        cases["bv_decide_groundwork_accepted"] = (bvok, "done")           # ACCEPTED, dormant support forced on
        cases["bv_decide_groundwork_forged"] = (bv, "comparator")
        with open(MATHLIB_FIXTURE) as fh:
            mfix = fh.read()
        if NATIVE_MARKER not in mfix or NATIVE_USE not in mfix or "import Mathlib.Tactic.Ring\n" not in mfix:
            return record("attacks", "mathlib fixture", False,
                          "tests/imports/mathlib_band.lean changed shape; update the attacks")
        cases["mathlib_lookalike"] = (mfix.replace("import Mathlib.Tactic.Ring\n",
                                                   "import Mathlib2.Tactic.Ring\n", 1), "imports")
        for label, tac in (("mathlib_native_decide", "native_decide"),
                           ("mathlib_decide_native", "decide +native")):
            helper = ("theorem native_helper : (List.range 100).foldl (· + ·) 0 = 4950 := by "
                      f"{tac}\n\n")
            cases[label] = (mfix.replace(NATIVE_MARKER, helper + NATIVE_MARKER, 1)
                            .replace(NATIVE_USE, NATIVE_USE + "  have _hn := native_helper\n", 1),
                            "comparator")
        glued = proof.replace("import SvGolf.Comb\n",
                              "import SvGolf.Comb/-c-/import Mathlib2.Tactic.Ring\n", 1)
        if glued == proof:
            return record("attacks", "glued import", False,
                          "the reference proof has no `import SvGolf.Comb` line; update the attack")
        cases["mathlib_glued_lookalike"] = (glued, "imports")
        planted = os.path.join(checkpy().package_dirs().get("mathlib", os.path.join(tmp, "no-mathlib")),
                               ".lake", "build", "lib", "lean", "Mathlib", "SvgolfAttackPlanted.olean")
        plant = ("\n#eval show IO Unit from do\n  IO.FS.writeFile " + checkpy().lean_string(planted)
                 + ' "planted by a solution\\n"\n')
        cases["mathlib_plant_free"] = (proof + plant, "integrity")
        cases["mathlib_plant_importing"] = (mfix + plant, "integrity")
        runs = []
        for label, (text, stage) in cases.items():
            path = os.path.join(tmp, f"{label}.lean")
            with open(path, "w") as fh:
                fh.write(text)
            # the plant attacks test the integrity TRIPWIRE, which the sandbox now makes unreachable (the
            # write is denied before it can happen): they run WITHOUT it; the `sandbox` step has their twins
            more = (["--sandbox", "off"] if label.startswith("mathlib_plant") or label == "bv_decide_subgoal_off"
                    else ["--sandbox", "require"] if label == "bv_decide_subgoal_sandbox"
                    else ["--time-limit", str(SLOW_LIMIT_S)] if label in ("slow_proof", "cpu_proof") else None)
            if label.startswith("bv_decide_groundwork"):
                runs.append((label, ref_sv, path, stage, bv_enabled_task_dir(tmp), []))
            else:
                runs.append((label, ref_sv, path, stage) + ((tdir, more) if more else ()))
        for label, text, stage in (("param_name", PARAM_W_SV, "extract"),
                                   ("narrow_param", NARROW_PARAM_SV, "extract")):
            sv = os.path.join(tmp, f"{label}.sv")
            with open(sv, "w") as fh:
                fh.write(text)
            runs.append((label, sv, ref_lean, stage))
        runs += [(f"gate:{f}", os.path.join(GATE_DIR, f), ref_lean, "source")
                 for f in GATE_FIXTURES]
        runs.append(("mathlib_band", ref_sv, MATHLIB_FIXTURE, "done"))   # the one ACCEPTED run
        # WP-S: the checker's secrets are not in the environment of the process that compiles the proof
        salt_env = dict(os.environ, SVGOLF_POSTSYNTH_SALT="wps-competition-salt",
                        CLAUDE_CODE_MESSAGING_TOKEN="wps-token", GITHUB_TOKEN="wps-gh-token")
        salt = proof.replace("import Submission.Design", "import Submission.Design\nimport Std.Internal.UV.System", 1) + SALT_PROBE
        salt_path = os.path.join(tmp, "host_env_salt.lean")
        with open(salt_path, "w") as fh:
            fh.write(salt)
        runs.append(("host_env_salt", ref_sv, salt_path, "done", tdir, [], salt_env))
        # the sv_comb tactic references under `import Mathlib.Tactic`, WITHOUT `sv_core_simp` (WP-B review, gate M)
        for tname, stem in TACTIC_REFERENCES:
            ttask = task_json(tname)
            refs = [r for r in ttask["references"] if os.path.basename(r["lean"]) == stem + ".lean"]
            if len(refs) != 1:
                return record("attacks", f"mathlib_tactics_{stem}", False,
                              f"task {tname} has no reference {stem}")
            with open(os.path.join(SVGOLF, "tasks", tname, refs[0]["lean"])) as fh:
                src = fh.read()
            head, sep, rest = src.partition("\n\n")
            if not head.startswith("import Submission.Design\n") or not sep:
                return record("attacks", f"mathlib_tactics_{stem}", False,
                              "the reference has no import block ending in a blank line; update the attack")
            text = (head.replace("import Submission.Design\n", "import Submission.Design\n"
                                 "import Mathlib.Tactic\n", 1)
                    + "\n\n" + rest)
            path = os.path.join(tmp, f"mathlib_tactics_{stem}.lean")
            with open(path, "w") as fh:
                fh.write(text)
            # what is tested is acceptance of the proof, not the task's wall-clock limit (which a loaded
            # machine misses: `sbox_bp` with Mathlib.Tactic did not finish in 215 s on a busy one)
            runs.append((f"mathlib_tactics_{stem}", os.path.join(SVGOLF, "tasks", tname, refs[0]["sv"]),
                         path, "done", os.path.join(SVGOLF, "tasks", tname), ["--time-limit", "900"]))
        want = [w for w in (getattr(args, "attack", None) or "").split(",") if w]
        if want:
            runs = [r for r in runs if any(w in r[0] for w in want)]
        for label, sv, lean, stage, *other in runs:
            try:
                res = run_check(other[0] if other else tdir, sv, lean,
                                extra + (other[1] if len(other) > 1 else []),
                                env=other[2] if len(other) > 2 else None,
                                script=CHECK_BV if label.startswith("bv_decide_groundwork") else None)
            finally:
                if os.path.exists(planted):      # the plant attacks leave their file behind
                    os.remove(planted)
            if stage == "done":
                ok = bool(res.get("accepted")) and res.get("stage") == "done"
                # the accepted bv_decide proof must have been accepted BY the re-verification of its axiom
                if ok and label == "bv_decide_groundwork_accepted":
                    ok = len((((res["stages"]["comparator"].get("result") or {}).get("bv_decide")) or {}).get("verified") or []) == 1
                detail = (f"accepted (stages: solution {res['stages']['solution']['seconds']} s, "
                          f"comparator {res['stages']['comparator']['seconds']} s, leanchecker "
                          f"{res['stages']['leanchecker']['seconds']} s)" if ok else
                          f"{verdict(res)} (want accepted): " + json.dumps(res.get("errors"))[:600])
            else:
                ok = not res.get("accepted") and res.get("stage") == stage
                # the native-evaluation attacks must be caught BY the axiom walk, which names the
                # generated axiom (`<decl>._native.native_decide.ax_*`, `<decl>._native.decide.ax_*`)
                if ok and label in ("mathlib_native_decide", "mathlib_decide_native"):
                    ok = "native_helper._native." in json.dumps(res.get("errors"))
                # the forged bv_decide axiom is rejected by POLICY (never passed `--bv-decide`), naming it; the
                # groundwork row, with the support forced on, by the RE-EVALUATION of its certificate
                if ok and label == "bv_decide_shaped":
                    ok = "`bv_decide` is not supported" in json.dumps(res.get("errors"))
                if ok and label == "bv_decide_groundwork_forged":
                    ok = "does not verify" in json.dumps(res.get("errors"))
                # a bv_decide proof is refused with the HINT, wherever it is refused
                if ok and label in ("bv_decide_subgoal_sandbox", "bv_decide_subgoal_off"):
                    msg = json.dumps(res.get("errors"))
                    ok = "external SAT solver (cadical)" in msg and "decide +kernel" in msg and (
                        "HINT:" in msg if label.endswith("sandbox") else "`bv_decide` is not supported" in msg)
                if ok and label.startswith("mathlib_plant"):
                    ok = "SvgolfAttackPlanted.olean" in json.dumps(res.get("errors"))
                # sleeping: stopped by the wall-clock backstop with few CPU seconds, and the rejection names the last
                # declaration that finished
                if ok and label == "slow_proof":
                    msg = " ".join(res.get("errors") or [])
                    sol = res["stages"]["solution"]
                    backstop = checkpy().solution_wall_backstop(SLOW_LIMIT_S)
                    ok = (msg.startswith(f"the proof did not compile within the {backstop:g} s wall-clock backstop")
                          and f"the last `{SLOW_LAST}" in msg and sol.get("exit") == 124
                          and sol.get("stopped_by") == "wall" and (sol.get("cpu_seconds") or 0) < SLOW_LIMIT_S
                          and sol.get("seconds", 0) >= backstop
                          and ((sol.get("progress") or {}).get("last") or {}).get("decls", "").startswith(SLOW_LAST)
                          and "[Kernel]" not in sol.get("messages", ""))
                # computing: stopped by the CPU limit, long before the backstop
                if ok and label == "cpu_proof":
                    msg = " ".join(res.get("errors") or [])
                    sol = res["stages"]["solution"]
                    ok = (msg.startswith(f"the proof did not compile within the {SLOW_LIMIT_S:g} s CPU limit")
                          and sol.get("exit") == 124 and sol.get("stopped_by") == "cpu"
                          and (sol.get("cpu_seconds") or 0) >= SLOW_LIMIT_S
                          and sol.get("seconds", 1e9) < checkpy().solution_wall_backstop(SLOW_LIMIT_S))
                detail = (f"{verdict(res)} (want {stage}): "
                          + (first_error(res) if ok else json.dumps(res.get("errors"))[:600]))
            good &= record("attacks", label, ok, detail, res["_seconds"])
        for f in GATE_OK_FIXTURES:
            res = run_check(tdir, os.path.join(GATE_DIR, f), None, ["--unproved"] + args.check_extra)
            src = (res.get("stages") or {}).get("source") or {}
            ok = clean_unproved(res) and src.get("findings") == []
            good &= record("attacks", f"gate-ok:{f}", ok,
                           f"{verdict(res)} (want unproved, no source findings): "
                           + ("every check that needs no proof passed" if ok else
                              json.dumps([res.get("errors"), src.get("findings")])[:600]),
                           res["_seconds"])
    return good


def sandbox_state():
    """(active, why): does the OS sandbox work on this machine (check/sandbox: mechanism present AND its
    self-test passes)? Decided in this process, which then goes back to `off`."""
    checkpy()
    sb = sys.modules["sandbox"]
    pol = sb.configure("auto", log=lambda *a: None)
    state = (pol.active, pol.reason)
    sb.configure("off")
    return state


def step_sandbox(args):
    """WP-S: the sandbox against real attacks, through `check.py --sandbox require` on `_example` (the
    attack texts are tests/sandbox/attacks.py; each is a thing a submission's Lean file could do before the
    sandbox, measured 2026-10-31):

      host_naive         the finding: reads /etc/hosts, writes a file outside the stage. WITHOUT the sandbox
                         (`--sandbox off`, the control that shows the attack is real): ACCEPTED, the file
                         exists. WITH it: REJECTED at `solution` ("operation not permitted"), no file
      host_catching      every action tried, every failure caught: ACCEPTED either way. Off: the marker is
                         written and the loopback listener hears a connection (and the integrity tripwire
                         rejects the overwritten Design.olean). On: every action BLOCKED, no marker, no
                         connection, `integrity` clean
      host_memory_bomb   stopped by the supervisor's resident-memory limit   -> solution (SVGOLF_MEMORY)
      host_output_flood  stopped by its output cap                           -> solution (SVGOLF_OUTPUT)
      host_cpu_bomb      stopped by the task's wall-clock limit (--time-limit 10) -> solution
      host_spawn_bomb    (WP-BV) default flags: no process can be started, the first spawn fails ("operation not
                         permitted"), nothing is left; GROUNDWORK (the dormant bv_decide support forced on through
                         tests/checker/check_bv_enabled.py): the granted `fork` lets a file start copies of lean
                         that start more, stopped by the memory limit, nothing left running (SVGOLF_MEMORY)
      host_cadical       (WP-BV) the solver `cadical`, used by hand. Default flags: nothing is granted, so every try,
                         the legitimate one (a CNF in the temporary directory) included, is BLOCKED. GROUNDWORK
                         (support forced on): a real `bv_decide` fact in the same file is accepted and re-verified;
                         cadical on a CNF in the temporary directory works; its proof written outside, a CNF read
                         from another directory, a shell and curl are all BLOCKED; off: the marker is written
      mathlib_plant_*    the integrity-tripwire attacks with the sandbox ON: the write that used to be
                         caught after the fact is denied                     -> solution, nothing planted

    Skipped, with a message, where the machine has no sandbox mechanism (or it fails its self-test)."""
    active, why = sandbox_state()
    if not active:
        return record("sandbox", "attacks", True, f"SKIPPED: the OS sandbox is not available here ({why})")
    sys.path.insert(0, os.path.join(HERE, "sandbox"))
    import attacks as A
    tdir = os.path.join(SVGOLF, "tasks", "_example")
    task = task_json("_example")
    ref_sv = os.path.join(tdir, task["references"][0]["sv"])
    with open(os.path.join(tdir, task["references"][0]["lean"])) as fh:
        proof = fh.read()
    good = True
    with tempfile.TemporaryDirectory(prefix="svgolf-sandbox-attacks-") as tmp:
        tmp = os.path.realpath(tmp)
        secret_dir = os.path.join(tmp, "elsewhere")
        os.makedirs(secret_dir)
        secret = os.path.join(secret_dir, "secret.txt")
        with open(secret, "w") as fh:
            fh.write("another competitor's file\n")
        listener = A.Listener()
        extra0 = [x for x in args.check_extra if x not in ("--sandbox", args.sandbox)] + ["--no-score"]

        def lean_file(label, body, imports=A.EXTRA_IMPORTS, base=None, **fill):
            text = (base or proof).replace("import Submission.Design", "import Submission.Design\n" + imports.rstrip("\n"), 1) + body
            path = os.path.join(tmp, label + ".lean")
            with open(path, "w") as fh:
                fh.write(A.fill(text, **fill))
            return path

        def run(label, path, mode, more=(), env=None, sv=ref_sv, script=None):
            e = dict(os.environ, **(env or {}))
            e.setdefault("SVGOLF_POSTSYNTH_SALT", "wps-competition-salt")
            return run_check(bv_enabled_task_dir(tmp) if script else tdir, sv, path, extra0 + ["--sandbox", mode, "--stage-dir", os.path.join(tmp, "stage-" + re.sub(r"[^A-Za-z0-9]+", "-", label))]
                             + list(more), env=e, script=script)

        def verdict_line(res, want):
            return f"{verdict(res)} (want {want}): " + first_error(res)

        # `--attack host_cadical` runs the sandbox attacks whose label contains one of the substrings
        want = [w for w in (getattr(args, "attack", None) or "").split(",") if w]

        def wanted(label):
            return not want or any(w in label for w in want)

        # ---- host_naive, off then on
        if wanted("host_naive"):
            marker = os.path.join(tmp, "marker-naive-off")
            res = run("naive-off", lean_file("naive-off", A.NAIVE, marker=marker), "off")
            ok = bool(res.get("accepted")) and os.path.exists(marker) and "sandbox" not in res
            good &= record("sandbox", "host_naive (control, --sandbox off)", ok,
                           "ACCEPTED and the file outside the stage exists: the attack is real" if ok else
                           f"{verdict(res)}; marker exists: {os.path.exists(marker)}", res["_seconds"])
            marker = os.path.join(tmp, "marker-naive-on")
            res = run("naive-on", lean_file("naive-on", A.NAIVE, marker=marker), "require")
            msg = json.dumps(res.get("errors"))
            ok = (not res.get("accepted") and res.get("stage") == "solution" and "operation not permitted" in msg
                  and not os.path.exists(marker) and (res.get("sandbox") or {}).get("active") is True)
            good &= record("sandbox", "host_naive", ok, verdict_line(res, "solution, operation not permitted")
                           + f"; marker exists: {os.path.exists(marker)}", res["_seconds"])

        # ---- host_catching, off then on
        for mode in (("off", "require") if wanted("host_catching") else ()):
            marker = os.path.join(tmp, f"marker-catching-{mode}")
            before = len(listener.seen)
            fills = dict(marker=marker, home=os.path.expanduser("~"), secret=secret, stage=os.path.join(tmp, "stage-catching-" + mode),
                         port=listener.port)
            res = run("catching-" + mode, lean_file("catching-" + mode, A.CATCHING, **fills), mode)
            msgs = ((res.get("stages") or {}).get("solution") or {}).get("messages", "")
            ex = [ln for ln in msgs.splitlines() if ln.startswith("EXPLOIT ")]
            blocked = [ln for ln in ex if ": BLOCKED" in ln]
            heard = len(listener.seen) - before
            if mode == "off":
                # the tripwire sees the overwritten Design.olean (and nothing else)
                ok = (res.get("stage") == "integrity" and os.path.exists(marker) and heard >= 1 and len(ex) >= 10)
                detail = (f"{verdict(res)}; marker exists: {os.path.exists(marker)}; the listener heard {heard} "
                          f"connection(s); {len(blocked)} of {len(ex)} actions blocked (want rejected at integrity)")
            else:
                # every action is denied, except listing the environment: that is allowed and shows the
                # allowlist (no SVGOLF_ variable, no token)
                dump = [ln for ln in ex if ln.startswith("EXPLOIT environment dump: OK")]
                ok = (bool(res.get("accepted")) and len(ex) >= 10 and len(blocked) == len(ex) - 1
                      and len(dump) == 1 and "SVGOLF" not in dump[0] and "TOKEN" not in dump[0]
                      and not os.path.exists(marker) and heard == 0
                      and (res["stages"].get("integrity") or {}).get("changed") == [])
                detail = (f"{verdict(res)}; {len(blocked)} of {len(ex)} actions BLOCKED (the allowed one lists an "
                          f"environment with no secret in it); marker exists: "
                          f"{os.path.exists(marker)}; the listener heard {heard} connection(s)")
                if not ok:
                    detail += " :: " + msgs[:600].replace("\n", " | ")
            good &= record("sandbox", f"host_catching ({'control, --sandbox off' if mode == 'off' else 'require'})",
                           ok, detail, res["_seconds"])
        listener.close()

        # ---- host_cadical (WP-BV): the solver a bv_decide compile COULD be allowed to start, used by hand.
        # bv_decide is not supported (decided 2026-11-01): by default the sandbox grants nothing, and every try, the
        # legitimate one included, is BLOCKED. The groundwork rows force the dormant support on (CHECK_BV) and show what
        # the grant would be: the legitimate run works, the abuses are blocked, a real bv_decide fact in the same
        # file is accepted and re-verified.
        bvbase = proof.replace("/-- **The reference solution**", BV_HELPER, 1).replace(
            "theorem solution : Goal := by\n", "theorem solution : Goal := by\n  have _hbv := bv_helper\n", 1)
        if not wanted("host_cadical"):
            pass
        elif "_hbv := bv_helper\n  intro" not in bvbase:
            good &= record("sandbox", "host_cadical", False, "the reference proof changed shape; update the attack")
        else:
            secret_cnf = os.path.join(secret_dir, "secret.cnf")
            with open(secret_cnf, "w") as fh:
                fh.write("p cnf 1 2\n1 0\n-1 0\n")
            names = ("cadical in the temporary directory", "cadical writes its proof outside",
                     "cadical reads another directory's file", "spawn a shell", "spawn curl")
            # default flags: nothing granted, nothing works (the plain reference proof: it may not use bv_decide)
            marker = os.path.join(tmp, "marker-cadical-default")
            res = run("cadical-default", lean_file("cadical-default", A.CADICAL, A.EXTRA_IMPORTS, marker=marker,
                                                   secretcnf=secret_cnf), "require")
            msgs = ((res.get("stages") or {}).get("solution") or {}).get("messages", "")
            ex = {ln.split(":")[0][len("EXPLOIT "):]: ln for ln in msgs.splitlines() if ln.startswith("EXPLOIT ")}
            blocked = [n for n in names if ": BLOCKED" in ex.get(n, "")]
            ok = (bool(res.get("accepted")) and len(blocked) == len(names) and not os.path.exists(marker))
            detail = (f"{verdict(res)}; {len(blocked)} of {len(names)} tries BLOCKED, the legitimate cadical run included "
                      f"(the Spec grants no solver, no fork, no temporary directory); marker exists: {os.path.exists(marker)}")
            if not ok:
                detail += " :: " + msgs[:700].replace("\n", " | ")
            good &= record("sandbox", "host_cadical (default flags: nothing granted)", ok, detail, res["_seconds"])
            # the dormant groundwork, support forced on
            for mode in ("off", "require"):
                marker = os.path.join(tmp, f"marker-cadical-{mode}")
                res = run("cadical-" + mode, lean_file("cadical-" + mode, A.CADICAL, A.EXTRA_IMPORTS + "import Std.Tactic.BVDecide\n",
                                                       base=bvbase, marker=marker, secretcnf=secret_cnf), mode, script=CHECK_BV)
                msgs = ((res.get("stages") or {}).get("solution") or {}).get("messages", "")
                ex = {ln.split(":")[0][len("EXPLOIT "):]: ln for ln in msgs.splitlines() if ln.startswith("EXPLOIT ")}
                cmp_ = (((res.get("stages") or {}).get("comparator") or {}).get("result") or {}).get("bv_decide") or {}
                legit = ex.get("cadical in the temporary directory", "")
                if mode == "off":
                    # the control: nothing stops the file, which writes the marker (and reads the other file)
                    ok = (bool(res.get("accepted")) and os.path.exists(marker) and ": OK" in legit
                          and "EXPLOIT cadical reads another directory's file: OK" in msgs)
                    detail = (f"{verdict(res)}; marker exists: {os.path.exists(marker)} (want accepted, marker written)")
                else:
                    blocked = [n for n in names[1:] if ": BLOCKED" in ex.get(n, "")]
                    ok = (bool(res.get("accepted")) and ": OK" in legit and len(blocked) == 4
                          and not os.path.exists(marker) and len(cmp_.get("verified") or []) == 1
                          and (res["stages"].get("integrity") or {}).get("changed") == [])
                    detail = (f"{verdict(res)}; the legitimate cadical run OK: {': OK' in legit}; {len(blocked)} of 4 abuses "
                              f"BLOCKED; marker exists: {os.path.exists(marker)}; bv_decide axioms verified: "
                              f"{len(cmp_.get('verified') or [])}")
                    if not ok:
                        detail += " :: " + msgs[:700].replace("\n", " | ")
                good &= record("sandbox", f"host_cadical (groundwork: support forced on, "
                               f"{'control, --sandbox off' if mode == 'off' else 'require'})", ok, detail, res["_seconds"])

        # ---- resource bombs (limits lowered so that they fire in seconds)
        for label, body, env, msg_want, more in (
                ("host_memory_bomb", A.MEMORY, {"SVGOLF_SANDBOX_RSS_MB": "1500"}, "SVGOLF_MEMORY", ()),
                ("host_output_flood", A.OUTPUT, {"SVGOLF_SANDBOX_OUT_MB": "4"}, "SVGOLF_OUTPUT", ()),
                ("host_cpu_bomb", A.SPIN, {}, "did not compile within the 10 s CPU limit", ("--time-limit", "10")),
                # by default no process can be started at all (no fork): the file's first spawn fails
                ("host_spawn_bomb (default flags: no fork)", A.SPAWN, {}, "operation not permitted", ()),
                # the dormant groundwork, support forced on: the grant lets lean copies start, the memory limit stops them
                ("host_spawn_bomb (groundwork: support forced on)", A.SPAWN, {"SVGOLF_SANDBOX_RSS_MB": "1500"},
                 "SVGOLF_MEMORY", ())):
            if not wanted(label):
                continue
            res = run(label, lean_file(label.split(" ")[0] + ("-gw" if "groundwork" in label else ""), body), "require", more, env,
                      script=CHECK_BV if "groundwork" in label else None)
            ok = (not res.get("accepted") and res.get("stage") == "solution" and msg_want in json.dumps(res.get("errors")))
            if label.startswith("host_spawn_bomb"):
                # the whole process group died with the compile: no copy of the bomb's script is still running
                time.sleep(2)
                left = subprocess.run(["pgrep", "-f", "bomb.lean"], capture_output=True, text=True).stdout.split()
                ok = ok and not left
            good &= record("sandbox", label, ok, verdict_line(res, f"solution, {msg_want}"), res["_seconds"])

        # ---- the tripwire attacks, sandbox ON
        try:
            if not wanted("mathlib_plant"):
                raise StopIteration
            with open(MATHLIB_FIXTURE) as fh:
                mfix = fh.read()
            planted = os.path.join(checkpy().package_dirs().get("mathlib", os.path.join(tmp, "no-mathlib")),
                                   ".lake", "build", "lib", "lean", "Mathlib", "SvgolfAttackPlanted.olean")
            plant = ("\n#eval show IO Unit from do\n  IO.FS.writeFile " + checkpy().lean_string(planted)
                     + ' "planted by a solution\\n"\n')
            for label, text in (("mathlib_plant_free", proof + plant), ("mathlib_plant_importing", mfix + plant)):
                path = os.path.join(tmp, label + ".lean")
                with open(path, "w") as fh:
                    fh.write(text)
                try:
                    res = run(label, path, "require")
                    ok = (not res.get("accepted") and res.get("stage") == "solution"
                          and "operation not permitted" in json.dumps(res.get("errors"))
                          and not os.path.exists(planted))
                    good &= record("sandbox", label + " (sandbox ON)", ok,
                                   verdict_line(res, "solution, operation not permitted")
                                   + f"; planted file exists: {os.path.exists(planted)}", res["_seconds"])
                finally:
                    if os.path.exists(planted):
                        os.remove(planted)
        except StopIteration:
            pass
        except OSError as e:
            good &= record("sandbox", "mathlib_plant (sandbox ON)", False, str(e))
    return good


def attack_lean(t, a):
    """The proof file an attack of tests/expected.json is submitted with: None (no `lean`: `--unproved`), the task's
    first reference proof (`lean: "reference"`), or the reference proof it names (`lean: "reference/<stem>.lean"`, one
    of task.json's `references`: a task with several proved references, e.g. fdivp's Newton divider). Any other value
    is an error, never a silent `--unproved`."""
    want = a.get("lean")
    if want is None:
        return None
    task = task_json(t)
    if want == "reference":
        if statement_draft(t, task):
            raise ValueError(f"tasks/{t} is a statement draft (no proof file): its attacks run --unproved (no `lean`)")
        return first_lean(t, task)
    if want in [r["lean"] for r in task.get("references") or []]:
        return os.path.join(SVGOLF, "tasks", t, want)
    raise ValueError(f"lean {want!r} is neither `reference` nor a reference proof of tasks/{t}/task.json")


def step_design_attacks(tasks, expected, args):
    """The designs of tests/<task>/attacks/ (ls-sv/Yosys disagreements), through
    `check.py --unproved` (`lean: "reference"`: with the task's first reference proof, as
    in a submission; `lean: "reference/<stem>.lean"`: with that reference's proof): rejected
    at their expected stage. `postsynth_alone`
    (`rejects` or `passes`): the postsynth check with the source gate (and so
    the fourstate stage, which only check.py runs) bypassed, i.e. what it would
    do on its own for a design the static rules refuse."""
    good = True
    for t in tasks:
        tdir = os.path.join(SVGOLF, "tasks", t)
        for stem, a in expected["tasks"][t].get("attacks", {}).items():
            sv = design_path(t, "attacks", stem, a)
            pmode = a.get("postsynth_mode", "light")
            # `lean: "reference"` (or `reference/<stem>.lean`): the design is submitted WITH that reference
            # proof, which must fail on it (a correct-looking netlist that is wrong on some input: the attacks
            # of the fdivp proofs); otherwise the check runs without a proof (`--unproved`)
            try:
                lean = attack_lean(t, a)
            except ValueError as e:
                good &= record("attacks", f"{t}/attacks/{stem}", False, str(e))
                continue
            res = run_check(tdir, sv, lean, ([] if lean else ["--unproved"]) + a.get("args", [])
                            + args.check_extra, postsynth_mode=pmode)
            ok = not res.get("accepted") and res.get("stage") == a["stage"]
            if ok and a["stage"] == "unproved":
                ok = clean_unproved(res)          # the advisory attacks: a clean run, exit 0, its sentence a note
            if ok and a.get("message_contains"):
                # a rejection's phrase is in `errors`; a clean `--unproved` run has none, its sentence is in `notes`;
                # a list: one of its phrases (the entry's `why` says why there is more than one)
                text = " ".join(res.get("errors") or res.get("notes") or [])
                want_m = a["message_contains"]
                ok = any(m in text for m in (want_m if isinstance(want_m, list) else [want_m]))
            ps = (res.get("stages") or {}).get("postsynth") or {}
            extra = (f" [{ps.get('mismatches')} of {ps.get('vectors')} vectors differ]"
                     if ps.get("mismatches") else
                     f" [ls-sv: {ps.get('unsupported_runs')} of {ps.get('vectors')} runs "
                     "UNSUPPORTED]" if ps.get("unsupported_runs") else "")
            good &= record("attacks", f"{t}/attacks/{stem}", ok,
                           f"{verdict(res)} (want {a['stage']}){extra}: "
                           + (first_error(res) if ok else json.dumps(res.get("errors"))[:600]),
                           res["_seconds"])
            if a.get("functional") == "warns":
                # the advisory functional smoke check: the design disagrees with the task's
                # function, the result says so (ONE `warnings` line, `functional` with examples),
                # and the stage above is unchanged
                f, w = ps.get("functional") or {}, res.get("warnings") or []
                fok = (f.get("mismatches", 0) > 0 and 1 <= len(f.get("examples", [])) <= 3
                       and len(w) == 1 and w[0].startswith("functional: the design disagrees")
                       and f.get("checked") == ps.get("vectors"))
                good &= record("attacks", f"{t}/attacks/{stem} functional warning", fok,
                               w[0][:200] if fok else f"functional {f}, warnings {w}")
            elif a.get("functional") == "agrees":
                # a correct design the checker accepts up to the proof: no mismatch, no warning
                f = ps.get("functional") or {}
                fok = (f.get("mismatches") == 0 and f.get("checked") == ps.get("vectors")
                       and "unchecked" not in f and "warnings" not in res)
                good &= record("attacks", f"{t}/attacks/{stem} functional agrees", fok,
                               f"{f.get('checked')} of {ps.get('vectors')} vectors agree with the "
                               "oracle" if fok else f"functional {f}, warnings {res.get('warnings')}")
            if "tactics" in a:
                # the advisory `--tactics` pre-check (in the entry's `args`): in or out of the
                # sv_comb tactics' fragment, with the tactic's own message
                want_t, got_t = a["tactics"], res.get("tactics") or {}
                tok = (got_t.get("in_fragment") is want_t["in_fragment"]
                       and want_t.get("message_contains", "") in got_t.get("message", "")
                       and (want_t["in_fragment"] is not True or got_t.get("message") == "ok")
                       and bool(got_t.get("lowered")) == bool(want_t.get("lowered"))
                       and "seconds" in (res.get("stages") or {}).get("tactics", {}))
                good &= record("attacks", f"{t}/attacks/{stem} tactics", tok,
                               f"in_fragment {got_t.get('in_fragment')}: {got_t.get('message')}"
                               + (f" [{res['stages']['tactics']['seconds']} s]" if tok else ""))
            want = a.get("postsynth_alone")
            if want is None:
                continue
            t0 = time.time()
            with tempfile.TemporaryDirectory(prefix="svgolf-ps-") as work:
                try:
                    r = postsynth.check_design(tdir, sv, work, gate=False, mode=pmode)
                    got, what = "passes", f"no difference on {r['vectors']} vectors ({pmode})"
                except postsynth.Reject as e:
                    rec = e.info.get("record") or {}
                    got = "rejects"
                    what = f"[{pmode}] " + e.msg.splitlines()[0] + (
                        f" (harvested constants: {rec.get('harvested_constants')})"
                        if rec.get("harvested_constants") else "")
                except Exception as e:   # noqa: BLE001  (reported, never passes silently)
                    got, what = "error", f"{type(e).__name__}: {str(e).splitlines()[0][:200]}"
            good &= record("attacks", f"{t}/attacks/{stem} postsynth alone (gate bypassed)",
                           got == want, f"{got} (want {want}): {what}", time.time() - t0)
            if a.get("postsynth_light") and pmode == "full":
                # the sampling boundary between the modes, pinned where an entry documents it
                t0 = time.time()
                with tempfile.TemporaryDirectory(prefix="svgolf-ps-") as work:
                    try:
                        r = postsynth.check_design(tdir, sv, work, gate=False, mode="light")
                        lgot, lwhat = "passes", f"no difference on {r['vectors']} vectors (light)"
                    except postsynth.Reject as e:
                        rec = e.info.get("record") or {}
                        lgot = "rejects"
                        lwhat = f"[light] {rec.get('mismatches')} of {rec.get('vectors')} differ"
                    except Exception as e:   # noqa: BLE001  (reported, never passes silently)
                        lgot, lwhat = "error", f"{type(e).__name__}: {str(e).splitlines()[0][:200]}"
                good &= record("attacks", f"{t}/attacks/{stem} postsynth alone, LIGHT mode",
                               lgot == a["postsynth_light"],
                               f"{lgot} (want {a['postsynth_light']}): {lwhat}", time.time() - t0)
    return good


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def summary(t_start):
    print("\n== summary " + "=" * 68)
    print(f"{'step':<11} {'checks':>6} {'failed':>6} {'time':>8}")
    for s in STEPS:
        rows = [r for r in RESULTS if r[0] == s]
        if not rows:
            continue
        secs = sum(r[4] or 0 for r in rows)
        print(f"{s:<11} {len(rows):>6} {sum(not r[2] for r in rows):>6} {secs:>7.0f}s")
    bad = [r for r in RESULTS if not r[2]]
    print(f"{'total':<11} {len(RESULTS):>6} {len(bad):>6} {time.time() - t_start:>7.0f}s")
    for r in bad:
        print(f"FAILED {r[0]}: {r[1]}: {r[3].splitlines()[0][:200] if r[3] else ''}")
    print("run:", "PASS" if not bad else "FAIL")
    return not bad


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--only", help="comma-separated tasks (default: all)")
    ap.add_argument("--skip", default="", help=f"comma-separated steps to skip, of {STEPS}")
    ap.add_argument("--full", action="store_true",
                    help="the full (heavy, exhaustive) simulation plans; hours")
    ap.add_argument("--attack", help="comma-separated substrings: run only the checker attacks of "
                    "the `attacks` step (the `_example` submissions written by this script) "
                    "whose label contains one of them, and none of the designs of "
                    "tests/<task>/attacks/ (e.g. `--attack mathlib`)")
    ap.add_argument("--sandbox", choices=("off", "auto", "require"), default="auto",
                    help="check.py's --sandbox for every run of this script (default auto: used where the "
                    "mechanism exists). The `sandbox` step always runs its attacks with `require` and "
                    "skips, with a message, where there is no mechanism")
    ap.add_argument("--update-scores", action="store_true",
                    help="write the measured scores into tests/expected.json")
    args = ap.parse_args()
    skip = {s for s in args.skip.split(",") if s}
    if skip - set(STEPS):
        ap.error(f"unknown steps {sorted(skip - set(STEPS))} (known: {STEPS})")
    tasks = tasks_on_disk()
    if args.only:
        only = args.only.split(",")
        if set(only) - set(tasks):
            ap.error(f"unknown tasks {sorted(set(only) - set(tasks))} (known: {tasks})")
        tasks = [t for t in tasks if t in only]
    expected = load_json(EXPECTED)
    args.expected_tasks = expected["tasks"]        # (the statement-draft goalposts' scores, step_drafts)
    state, ppath, why = ppa_state()
    if state == "present":
        os.environ["SVGOLF_PPA_REQUIRE_LIB"] = "1"     # the real-library tests of score/test_ppa.py cannot skip silently
    # check.py's own trusted build (`lake build SvGolf tasks`) is part of the
    # build step; without it, the first check.py run does it.
    args.check_extra = ["--no-trusted-build"] if "build" not in skip else []
    args.check_extra += ["--sandbox", args.sandbox]
    t_start = time.time()
    print(f"svGolf tests: tasks {tasks}, steps {[s for s in STEPS if s not in skip]}"
          f"{', full validation' if args.full else ''}; lean wrap: {' '.join(WRAP) or '(none)'}",
          flush=True)
    print("sky130 PPA columns: " + {"present": f"the pinned liberty is present ({ppath}): the references run "
                                    "`--ppa require`, SVGOLF_PPA_REQUIRE_LIB=1",
                                    "absent": f"the pinned liberty is ABSENT ({why}): the PPA checks are SKIPPED with a "
                                    "message, the references run `--ppa auto`",
                                    "invalid": f"{ppath} is NOT the pinned liberty ({why}): a failure"}[state],
          flush=True)
    if "layout" not in skip:
        step_layout(tasks_on_disk(), expected)
    if "build" not in skip:
        if not step_build():
            print("the build failed: the check.py steps need it, stopping", flush=True)
            summary(t_start)
            return 1
    if "unit" not in skip:
        step_unit()
    if "comparator" not in skip:
        step_comparator()
    if "leaderboard" not in skip:
        step_leaderboard()
    if "modes" not in skip:
        step_modes(tasks, expected, args)
    if "canon" not in skip:
        step_canon(tasks, expected, args)
    if "references" not in skip:
        step_references(tasks, expected, args)
    if "drafts" not in skip:
        step_drafts(tasks, expected, args)
    if "negatives" not in skip:
        step_negatives(tasks, expected, args)
    if "baselines" not in skip:
        step_baselines(tasks, expected, args)
    if "baseline-proofs" not in skip:
        step_baseline_proofs(tasks, expected, args)
    if "ppa" not in skip:
        step_ppa(tasks, expected, args)
    if "validate" not in skip:
        step_validate(tasks, expected, args)
    if "attacks" not in skip:
        if not args.only or "_example" in tasks:
            step_attacks(args)
        if not args.attack:
            step_design_attacks(tasks, expected, args)
    # `--attack host_cadical` also selects the sandbox attacks whose label contains the substring
    sandbox_wanted = not args.attack or any(
        w in lbl for w in args.attack.split(",") if w
        for lbl in ("host_naive", "host_catching", "host_cadical", "host_memory_bomb", "host_output_flood",
                    "host_cpu_bomb", "host_spawn_bomb", "mathlib_plant"))
    if "sandbox" not in skip and sandbox_wanted:
        if not args.only or "_example" in tasks:
            step_sandbox(args)
    if args.update_scores:
        expected["flow"] = current_flow()
        expected["flow_seq"] = current_flow("seq")
        with open(EXPECTED, "w") as fh:
            json.dump(expected, fh, indent=2)
            fh.write("\n")
        print(f"wrote the measured scores to {rel(EXPECTED)}; review the diff")
    return 0 if summary(t_start) else 1


if __name__ == "__main__":
    sys.exit(main())
