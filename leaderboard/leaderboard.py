#!/usr/bin/env python3
"""svGolf leaderboard: records, verification, the ranked boards and the Pareto frontier.

Records of accepted submissions, their verification and the ranked boards: ranked
by area x time (decided 2026-11-05: the sky130 A0' area in um^2 times the time in
ps, the critical-path delay or cycles x the clock period of a clocked task;
`combined.py` defines it once), the one ranked number, lower is better. The
Pareto frontier of the two factors (`pareto`, the board's `layer` column) is an
exploration view, like the extra columns area in GE and depth: it ranks nothing.

    leaderboard.py add --task T --player P [--assisted-by X ...] --sv solution.sv --lean Solution.lean
                       [--notes TEXT] [--from-check RESULT.json] [--date YYYY-MM-DD]
                       [--postsynth full|light]
    leaderboard.py verify [--task T] [--offline | --full]
    leaderboard.py pareto --task T [--format text|json] [--unassisted] [--axes A,B,...]
    leaderboard.py board  --task T [--format md|json] [--unassisted] [--all-flows]
    leaderboard.py export --out FILE.md [--all-flows]
    leaderboard.py seed-references [--task T]
    leaderboard.py submit --task T --record HASH [--dry-run] [--repo URL]

One record per ACCEPTED submission, written to
`leaderboard/data/<task>/<record_hash>.json` next to copies of the two
submitted files (`<record_hash>.sv`, `<record_hash>.lean`), so an entry can be
re-verified. The record format, the policies (the ranked number, the Pareto
frontier, optional depth budget, staleness) and the verification levels are documented in
`leaderboard/README.md`; svgolf/README.md has the short version.

Everything that decides anything is a PURE function of its arguments (record
building, validation, hashing, dominance, ranking, rendering). The clock, git,
the file system and the subprocesses (check.py, score.py) are touched only by
the `cmd_*` functions and the small helpers under "environment". In
particular the submission date is never read inside a pure function: it is a
`--date` argument, defaulting to today's UTC date in `cmd_add` only.

Python 3, standard library only. check.py and score.py are run as
subprocesses (they need python3.12 with pyslang; `$SVGOLF_PYTHON` or
`python3.12` on PATH is used for them, this file runs on any Python 3.9+).
Exit status: 0 success, 1 refused / verification failed, 2 usage or
infrastructure error.
"""

import argparse
import copy
import datetime
import hashlib
import importlib.util
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))


def _load_combined():
    """leaderboard/combined.py (the area x time product, defined once), by path: this file is also loaded by path
    (site/build.py, check.py, the tests), with its directory not on sys.path."""
    spec = importlib.util.spec_from_file_location("svgolf_combined", os.path.join(HERE, "combined.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


combined = _load_combined()
SVGOLF = os.path.dirname(HERE)
DEFAULT_DATA = os.path.join(HERE, "data")
DEFAULT_TASKS = os.path.join(SVGOLF, "tasks")
CHECK_PY = os.path.join(SVGOLF, "check.py")
SCORE_PY = os.path.join(SVGOLF, "score", "score.py")
PPA_PY = os.path.join(SVGOLF, "score", "ppa.py")
PPA_PINS = os.path.join(SVGOLF, "score", "ppa_pins.json")
PPA_MAPPED_PINS = os.path.join(SVGOLF, "score", "ppa_mapped_pins.json")
PPA_MAPPED_SCRIPT = os.path.join(SVGOLF, "score", "ppa_mapped.ys")
# THE ASAP7 VIEW (decided 2026-11-09: a dropdown on the front page lets the reader see the golf scores on sky130 or on
# ASAP7). sky130 stays the default and the records' own columns; the ASAP7 A0' columns of every
# record, proved reference and baseline (score/ppa.py --pdk asap7 on the same scored netlist) are DERIVED data kept
# beside the records, one file per task (leaderboard/asap7/<task>.json, `asap7 --write`), bound to each record by its
# design's sha256, canonical text, canonical RTLIL and scored netlist, and re-derived by `verify` and `asap7
# --rescore`. Not in the records: adding a column after the fact would change every record's hash (its identity and its
# page's address) and need every record re-checked, a player's included, for numbers that are a pure function of
# the scored netlist the record already pins. See "The ASAP7 view" below and leaderboard/README.md.
PDKS = ("sky130", "asap7")
DEFAULT_PDK = "sky130"
PPA_PINS_ASAP7 = os.path.join(SVGOLF, "score", "ppa_pins_asap7.json")
ASAP7_DIR = os.path.join(HERE, "asap7")
EXPECTED_JSON = os.path.join(SVGOLF, "tests", "expected.json")

SCHEMA = "svgolf-leaderboard-record/1"

# The post-synthesis check runs in one of two modes (check/postsynth.py, "TWO
# MODES"). OFFICIAL artifacts are always FULL: `add` and `verify --full` run
# check.py with `--postsynth full` unless `add --postsynth light` says
# otherwise, and then the record is marked `postsynth.mode: "light"` and shown
# so on the board. A record without `postsynth.mode` was made by a checker
# that had only the full check: it reads as "full".
POSTSYNTH_MODES = ("light", "full")
DEFAULT_POSTSYNTH_MODE = "full"

# The sky130 PPA columns (WP-X3, score/ppa.py) are the RANKED score (decided 11/03: sky130 A0' ranks,
# area um^2 and time ps; GE and depth are extra columns): an official `add` / `verify --full` runs
# check.py with `--ppa require` and the record carries check.py's `ppa` object as the optional
# top-level key `ppa` (additive, like `postsynth.mode`: the schema string is unchanged, and a record
# without the key, every record made before the columns existed, stays valid and verifies as it did,
# but is NOT RANKED until it is backfilled: checked again, which gives a record with the columns).
PPA_KEY = "ppa"
# Flow A1' (WP-X4): a real `abc -liberty` mapping of the same run's canonical RTLIL, recorded as the optional SUB-object
# `ppa.mapped` (an unranked research column set beside A0''s, with its own field names, version and hashes: A0' is the
# ranked flow, A1' an extra column). A record without it, every record made before WP-X4, stays valid and verifies as it did.
PPA_MAPPED_KEY = "mapped"
# The player whose records are the proved references (`seed-references`): PAR, the bar to beat (site/config.json's
# `reference_player` names the same player).
REFERENCE_PLAYER = "svgolf-reference"
OFFICIAL_PPA_MODE = "require"
# Every check an official artifact comes from runs its untrusted processes in the OS sandbox (WP-S): the
# mechanism missing, or failing its self-test, is an infrastructure error, never a record made without it.
OFFICIAL_SANDBOX_MODE = "require"

# THE CLOCKED RECORD FORMAT (decided 2026-11-07). A task whose kind is one of CLOCKED_KINDS is scored by the clocked
# flow and checked after synthesis at EVERY point of its task.json `postsynth.points` (check.py `score_clocked`), so:
# acceptance requires `stages.postsynth.points` (every point of the task, in full mode, every seed run, 0 mismatches);
# the record's `postsynth` keeps those points (`clocked_postsynth_record`); the record carries the flow of its kind
# (`checker.flow: "seq"`, and the hashes of svgolf_seq.ys and ge_seq.json); and the board, the rescore (`score.py
# --seq`) and the site's flow pin compare a record only with the current flow of its own kind (`task_flow`,
# `current_flow(svgolf, flow)`). A combinational record is unchanged: no `checker.flow` (it reads as "comb"), the
# vectors form of `postsynth`, the hashes of svgolf.ys and ge.json. check.py, check/postsynth.py and score/points.py
# name the same kinds; the tests hold the classification of every kind check.py knows to check.py's. `react-family` is
# the arbiter's kind (tasks/arbiter).
CLOCKED_KINDS = ("seq-family", "tx-family", "stream-family", "react-family")
COMB_FLOW, SEQ_FLOW = "comb", "seq"
# The scoring flows by name: the files whose sha256 are a record's `checker.script_sha256` and `checker.ge_table_sha256`
# (score/score.py `FLOWS`; canon.ys and the Yosys build are shared). Relative to score/.
FLOW_FILES = {COMB_FLOW: ("svgolf.ys", "ge.json"), SEQ_FLOW: ("svgolf_seq.ys", "ge_seq.json")}
# The seeds per point of the clocked post-synthesis check when task.json `postsynth.seeds` names none
# (check/postsynth.py `CLOCKED_DEFAULTS["seeds"]`; the tests compare the two)
CLOCKED_SEEDS_DEFAULT = 8
# What one seed of the clocked check counts besides its cycles, per kind (check/postsynth.py `clocked_seed`): the
# transactions of a tx-family or stream-family run, the segments of a react-family one; a seq-family run counts only
# its cycles
CLOCKED_SEED_UNIT = {"tx-family": "transactions", "stream-family": "transactions", "react-family": "segments"}

# The files whose content is the checker (and the pinned flow): their sha256
# go into every record (`checker.files`), so "which checker accepted this" is
# answerable even from a dirty working tree, and `verify` can say whether
# they have changed since. Paths relative to svgolf/.
CHECKER_FILES = (
    "check.py", "check/envelope.py", "check/postsynth.py", "check/Comparator.lean",
    "check/SvEval.lean", "score/score.py", "score/srcgate.py", "score/banlist.py",
    "score/fourstate.py", "score/canon.ys", "score/svgolf.ys", "score/ge.json",
    "score/ppa.py", "score/ppa_pins.json", "score/ppa_mapped.ys", "score/ppa_mapped_pins.json",
    "lean-toolchain", "lakefile.toml",
    # the clocked kinds' (2026-11-07): the clocked flow, its GE table, the clocked source rules (check.py
    # CLOCKED_TRUSTED, fingerprinted by its integrity tripwire too)
    "score/svgolf_seq.ys", "score/ge_seq.json", "check/clocked_rules.py",
)
# THE STATEMENT A RECORD WAS CHECKED UNDER (decided 2026-11-07, round 7b review M1). A record's `checker.statement`
# maps each trusted statement file it was checked under to its sha256: the task's statement module
# (task.json `statement.module`, e.g. tasks/add/Spec.lean) and every module of svgolf/ it imports, transitively
# (`statement_files`): SvGolf/Task.lean for every task, SvGolf/TaskSeq.lean and SvGolf/TaskReact.lean for the clocked
# kinds that rest on them, a task's own helper (tasks/fdivp/IEEE754.lean). A module outside svgolf/ (ls-sv's
# LeanModels, Mathlib) is not in it: the ls-sv revision is `lean_surfaces_revision`. The board, the site and `verify`
# compare a record only with the task's statement as it is now (`current_statement`): a record checked under
# another statement, or made before records named theirs, is stale and not ranked, whatever its score.
# The paths whose uncommitted changes mark a revision `+dirty` (the trusted
# base; the leaderboard's own files and the player material are not it).
DIRTY_PATHSPEC = ("check.py", "check", "score", "SvGolf", "lakefile.toml",
                  "lean-toolchain", "lake-manifest.json", "tasks/*/Spec.lean",
                  "tasks/*/IEEE754.lean", "tasks/*/task.json")

PLAYER_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]{0,31}")
SHA_RE = re.compile(r"[0-9a-f]{64}")
DATE_RE = re.compile(r"\d{4}-\d{2}-\d{2}(T\d{2}:\d{2}:\d{2}Z)?")
MAX_ASSISTED = 32
MAX_ASSIST_LEN = 120
MAX_NOTES = 2000

# Tactics and proof tools whose use is recorded when they occur in the Lean
# source (comments and string literals stripped). Detection is lexical: a
# convenience for readers of the board, not a claim about the proof term.
TACTIC_WATCH = (
    "sv_comb", "sv_cover", "sv_eq_norm", "sv_eq_norm_at", "sv_equations", "sv_interface",
    "sv_norm", "sv_norm_core", "sv_prove", "sv_rowmajor", "sv_simp", "sv_structure",
    "omega", "grind", "decide", "induction", "simp", "bv_decide", "native_decide",
)


class Refused(Exception):
    """A submission or record that must not be accepted; `.problems` lists why."""

    def __init__(self, problems):
        super().__init__("; ".join(problems))
        self.problems = list(problems)


# ---------------------------------------------------------------------------
# hashing and canonical JSON
# ---------------------------------------------------------------------------

def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def canonical_json(obj):
    """The canonical text a record is hashed as: sorted keys, no whitespace,
    ASCII only, no NaN/Infinity. (Floats are Python's shortest round-trip repr.)"""
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
                      allow_nan=False)


def compute_record_hash(rec):
    """sha256 of the canonical JSON of the record without its `record_hash`."""
    body = {k: v for k, v in rec.items() if k != "record_hash"}
    return sha256_bytes(canonical_json(body).encode("ascii"))


# ---------------------------------------------------------------------------
# Lean source facts (pure)
# ---------------------------------------------------------------------------

_CHAR_LIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")


def strip_lean(text):
    """`text` with Lean comments removed (nested block comments, `--` line
    comments, doc comments are block comments) and string-literal contents
    emptied. Line structure is kept: every newline survives, so a line is
    blank in the result iff it carried no code."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        c = text[i]
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if c == "\n":
                    out.append("\n")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append('""' + "\n" * text[i:j + 1].count("\n"))
            i = j + 1
        elif c == "'" and not (i > 0 and (text[i - 1].isalnum() or text[i - 1] in "_'")):
            m = _CHAR_LIT.match(text, i)
            if m:
                out.append("' '")
                i = m.end()
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def lean_code_lines(text):
    """The number of lines of `text` that carry code: comments (line, block,
    doc) and blank lines stripped. `import` and `namespace` lines count."""
    return sum(1 for ln in strip_lean(text).split("\n") if ln.strip())


def lean_imports(text):
    """The modules the file imports, from its header (comments stripped)."""
    toks = strip_lean(text).split()
    imports, i = [], 0
    while i < len(toks):
        t = toks[i]
        if t in ("public", "meta", "private") and i + 1 < len(toks) and toks[i + 1] == "import":
            i += 1
            continue
        if t != "import" or i + 1 >= len(toks):
            break
        mod = toks[i + 1]
        if mod == "all" and i + 2 < len(toks):
            mod = toks[i + 2]
            i += 1
        imports.append(mod)
        i += 2
    return imports


def lean_tactics(text):
    """The watched tactics that occur in the code (sorted)."""
    code = strip_lean(text)
    found = [t for t in TACTIC_WATCH
             if re.search(r"(?<![\w.'])" + re.escape(t) + r"(?![\w'])", code)]
    return sorted(found)


# ---------------------------------------------------------------------------
# normalization of the human-supplied fields (pure)
# ---------------------------------------------------------------------------

def _no_control(s):
    return not any(ord(c) < 32 or ord(c) == 127 for c in s)


def normalize_player(player):
    if not isinstance(player, str) or not PLAYER_RE.fullmatch(player):
        raise Refused([f"player handle {player!r} must match {PLAYER_RE.pattern} "
                       "(1 to 32 characters: letters, digits, `.`, `_`, `-`)"])
    return player


def normalize_assisted_by(items):
    """`assisted_by`: a list of free-text strings naming the tools and AI
    systems that helped write the design or the proof. Surrounding blanks are
    stripped, empty and duplicate entries are dropped (order kept), control
    characters are refused. An empty list is allowed (an unassisted claim)."""
    if items is None:
        return []
    if isinstance(items, str) or not isinstance(items, (list, tuple)):
        raise Refused(["assisted_by must be a list of strings"])
    out, problems = [], []
    for x in items:
        if not isinstance(x, str):
            problems.append(f"assisted_by entry {x!r} is not a string")
            continue
        s = " ".join(x.split()) if _no_control(x.replace("\t", " ")) else None
        if s is None:
            problems.append(f"assisted_by entry {x!r} contains control characters")
        elif len(s) > MAX_ASSIST_LEN:
            problems.append(f"assisted_by entry {s[:30]!r}... is longer than {MAX_ASSIST_LEN}")
        elif s and s not in out:
            out.append(s)
    if len(out) > MAX_ASSISTED:
        problems.append(f"assisted_by lists {len(out)} entries; at most {MAX_ASSISTED}")
    if problems:
        raise Refused(problems)
    return out


def normalize_notes(notes):
    if notes is None:
        return ""
    if not isinstance(notes, str) or len(notes) > MAX_NOTES:
        raise Refused([f"notes must be a string of at most {MAX_NOTES} characters"])
    return notes.strip()


def normalize_date(submitted_at):
    if not isinstance(submitted_at, str) or not DATE_RE.fullmatch(submitted_at):
        raise Refused([f"submitted_at {submitted_at!r} must be an ISO date YYYY-MM-DD "
                       "(or YYYY-MM-DDTHH:MM:SSZ)"])
    try:
        datetime.date.fromisoformat(submitted_at[:10])
    except ValueError:
        raise Refused([f"submitted_at {submitted_at!r} is not a calendar date"])
    return submitted_at


# ---------------------------------------------------------------------------
# tasks (pure)
# ---------------------------------------------------------------------------

def scoring_point(task):
    return {k: int(v) for k, v in task["scoring"]["params"].items()}


def effective_depth_budget(task):
    """The depth budget the board ranks under: the task's optional
    `leaderboard.depth_budget` (a ranking-only, "soft" budget) and/or its
    `scoring.depth_budget` (the checker's hard gate), the smaller one; None
    if neither is set."""
    vals = [v for v in ((task.get("leaderboard") or {}).get("depth_budget"),
                        (task.get("scoring") or {}).get("depth_budget")) if v is not None]
    return min(vals) if vals else None


def is_clocked_task(task):
    """Whether `task` (a task.json) is of a CLOCKED_KINDS kind."""
    return isinstance(task, dict) and task.get("kind") in CLOCKED_KINDS


def task_flow(task):
    """The scoring flow of `task`'s kind (FLOW_FILES): "seq" for a clocked kind, else "comb"."""
    return SEQ_FLOW if is_clocked_task(task) else COMB_FLOW


def record_flow(rec):
    """The flow a record says it was scored under: its `checker.flow`, "comb" when it names none (every
    combinational record, and every record made before the clocked format)."""
    c = rec.get("checker") if isinstance(rec, dict) else None
    return c.get("flow", COMB_FLOW) if isinstance(c, dict) else COMB_FLOW


def point_text(params):
    """A point as check.py names it ({"N": 3} -> "N=3"; check/envelope.py `point_str`), "default" for a
    parameterless top (the clocked check's name for it, check/postsynth.py `run_clocked`)."""
    return ",".join(f"{k}={v}" for k, v in params.items()) or "default"


def clocked_points(task):
    """The points of a clocked task's post-synthesis check, in check.py's order (`score_clocked`): the scoring point
    first unless the task's `postsynth.points` lists it, then those points; each {param: int}."""
    sp = scoring_point(task)
    pts = [{k: int(v) for k, v in p.items()} for p in ((task.get("postsynth") or {}).get("points") or [])]
    return ([] if sp in pts else [sp]) + pts


def clocked_seeds(task):
    """The seeds the clocked check runs per point: task.json `postsynth.seeds`, else the checker's default."""
    return (task.get("postsynth") or {}).get("seeds", CLOCKED_SEEDS_DEFAULT)


def task_leaderboard_problems(task):
    """Schema problems of the optional `leaderboard` field of a task.json."""
    lb = task.get("leaderboard")
    if lb is None:
        return []
    if not isinstance(lb, dict):
        return ["`leaderboard` must be an object"]
    problems = []
    for k, v in lb.items():
        if k.startswith("_"):
            continue
        if k != "depth_budget":
            problems.append(f"`leaderboard` has the unknown key {k!r} (known: depth_budget)")
        elif v is not None and (isinstance(v, bool) or not isinstance(v, int) or v < 1):
            problems.append("`leaderboard.depth_budget` must be a positive integer or null")
    return problems


# ---------------------------------------------------------------------------
# acceptance and record building (pure)
# ---------------------------------------------------------------------------

def _get(d, *path, default=None):
    for k in path:
        if not isinstance(d, dict) or k not in d:
            return default
        d = d[k]
    return d


def record_mode(ps):
    """The post-synthesis mode of a `postsynth` object (a check result's stage
    or a record's): its `mode`, "full" when it has none (a checker from before
    the light mode existed ran only the full check)."""
    return ps.get("mode", "full") if isinstance(ps, dict) else "full"


def acceptance_problems(res, task, sv_sha256, postsynth="full"):
    """Why `res` (check.py's result JSON) does not entitle the submission whose
    .sv has sha256 `sv_sha256` to a record for `task`. Empty list: it does.
    `postsynth` is the mode the record was asked for: a result whose
    post-synthesis check ran LIGHT is acceptable only for "light" (an official
    record needs the full check). Besides the verdict of every stage: the run
    built the trusted modules itself (`stages.trusted`), the solution stage ran
    under the task's own CPU limit and was not stopped, and check.py does not
    report the check INCOMPLETE (`incomplete`)."""
    if not isinstance(res, dict):
        return ["the check result is not a JSON object"]
    p = []
    if res.get("unproved_ok") or res.get("stage") == "unproved":
        p.append("this is the result of a `check.py --unproved` run: it checked no proof (its exit status 0 says "
                 "the design is admissible), and only a run with the Lean file can be recorded")
    if res.get("accepted") is not True:
        p.append(f"check.py did not accept the submission (accepted={res.get('accepted')!r}, "
                 f"stage {res.get('stage')!r})")
    if res.get("stage") != "done":
        p.append(f"the check stopped at stage {res.get('stage')!r}, not `done`")
    if res.get("errors"):
        p.append("the check reports errors: " + str(res["errors"][0])[:200])
    if res.get("task") != task.get("name"):
        p.append(f"the check result is for task {res.get('task')!r}, not {task.get('name')!r}")
    if _get(res, "stages", "source", "sha256") != sv_sha256:
        p.append("the check result is not about this .sv (stages.source.sha256 differs from "
                 "the sha256 of the submitted file)")
    if _get(res, "stages", "source", "findings"):
        p.append("the source gate reported findings")
    if not SHA_RE.fullmatch(str(_get(res, "stages", "source", "canonical_sha256", default=""))):
        p.append("the result has no canonical text hash (stages.source.canonical_sha256)")
    sc = res.get("score")
    if not (isinstance(sc, dict) and isinstance(sc.get("area_mge"), int)
            and isinstance(sc.get("depth"), int) and isinstance(sc.get("gates"), dict)):
        p.append("the result has no score (a check run with --no-score cannot be recorded)")
    else:
        if sc.get("params") != scoring_point(task):
            p.append(f"scored at {sc.get('params')}, not at the task's scoring point "
                     f"{scoring_point(task)}")
        budget = _get(task, "scoring", "depth_budget")
        if budget is not None and sc["depth"] > budget:
            p.append(f"depth {sc['depth']} exceeds the task's depth budget {budget}")
    if _get(res, "stages", "score", "gated") is not True:
        p.append("the score is not gated (an ungated score is not an svGolf score)")
    if not is_clocked_task(task) and (_get(res, "stages", "score", "flow", default=COMB_FLOW) != COMB_FLOW
                                      or (isinstance(sc, dict) and any(k in sc for k in CLOCKED_SCORE_KEYS))):
        p.append("the result carries the clocked flow's score, and a combinational task is scored by the "
                 "combinational flow (score/svgolf.ys, ge.json)")
    ps = _get(res, "stages", "postsynth")
    if is_clocked_task(task):
        p += clocked_acceptance_problems(res, task, postsynth)
    elif not (isinstance(ps, dict) and isinstance(ps.get("vectors"), int)
              and ps["vectors"] > 0 and ps.get("mismatches") == 0):
        p.append("the post-synthesis check did not pass (no `stages.postsynth` record with "
                 "mismatches 0: a result of an older checker, or a run without scoring)")
    elif record_mode(ps) not in POSTSYNTH_MODES:
        p.append(f"stages.postsynth.mode {record_mode(ps)!r} is neither 'light' nor 'full'")
    elif record_mode(ps) == "light" and postsynth != "light":
        p.append("the post-synthesis check ran in LIGHT mode (a subset of the vectors, for local "
                 "feedback): an official record needs the full check. Rerun check.py with "
                 "--postsynth full (or SVGOLF_POSTSYNTH=full), or record it as a light record "
                 "with `add --postsynth light`")
    comp = _get(res, "stages", "comparator", "result")
    allowed = set(task.get("allowed_axioms", ["propext", "Classical.choice", "Quot.sound"]))
    if not (isinstance(comp, dict) and comp.get("accepted") is True
            and isinstance(comp.get("axioms"), list)):
        p.append("the comparator did not accept (no `stages.comparator.result`)")
    else:
        extra = sorted(set(comp["axioms"]) - allowed)
        if extra:
            p.append(f"axioms outside the task's allowed set: {extra}")
    if _get(res, "stages", "solution", "exit") != 0:
        p.append("the solution stage did not succeed")
    # the board's own kernel check: the run built the trusted modules itself (else the comparator checked the goal
    # against whatever statement module was on disk), and the solution stage's own verdict is the task's limit's
    trusted = _get(res, "stages", "trusted")
    if not (isinstance(trusted, dict) and trusted.get("exit") == 0):
        p.append("the result has no `stages.trusted` with exit 0: the check did not build the trusted modules "
                 "(`check.py --no-trusted-build`), so its comparator checked the goal against whatever statement "
                 "module was on disk")
    sol = _get(res, "stages", "solution")
    if isinstance(sol, dict):
        limit = task.get("time_limit_s", 600)
        if sol.get("time_limit_s") != limit:
            p.append(f"the proof was checked under a time limit of {sol.get('time_limit_s')!r} s, not the task's "
                     f"{limit} CPU s (`check.py --time-limit`, or a checker from before the limit was recorded)")
        if sol.get("time_limit_counts") not in (None, "cpu"):
            p.append(f"the solution stage's limit counted {sol.get('time_limit_counts')!r}, not CPU seconds")
        cpu = sol.get("cpu_seconds")
        if isinstance(cpu, (int, float)) and isinstance(limit, (int, float)) and cpu > limit:
            p.append(f"the solution stage used {cpu} CPU s, over the task's {limit} s limit")
        if sol.get("stopped_by"):
            p.append(f"the solution stage was stopped at its {sol['stopped_by']} limit")
    # check.py's own completeness verdict (`incomplete_reasons`): a light check is acceptable only for a light record
    for why in res.get("incomplete") or []:
        if postsynth == "light" and str(why).startswith("the post-synthesis check ran LIGHT"):
            continue
        p.append("check.py reports the check INCOMPLETE: " + str(why)[:300])
    if res.get("complete") is False and not res.get("incomplete"):
        p.append("check.py reports the check INCOMPLETE")
    integ = _get(res, "stages", "integrity")
    if not isinstance(integ, dict) or integ.get("changed") or integ.get("changed_by_end"):
        p.append("the integrity stage is missing or reports changed files")
    if _get(res, "stages", "leanchecker", "exit") != 0:
        p.append("the leanchecker stage did not succeed")
    p += ppa_acceptance_problems(res)
    return p


def ppa_acceptance_problems(res):
    """Why the `ppa` object of a check result cannot enter a record. A result WITHOUT the key
    (a checker from before the columns, or `--ppa off`) is acceptable: its record has no PPA
    columns. A result that carries the key must carry a well-formed object, and an unavailable
    one (`{"available": false, "reason": ...}`) only if the run was `--ppa require`: under `auto`
    the pinned liberty may merely have been absent on that machine, and an official record is
    never the record of a missing file. (Under `require` an unavailable object is a design the
    pinned flow cannot weigh, with the loud reason: recorded as it is.)"""
    if "ppa" not in res:
        return []
    block = res["ppa"]
    bad = validate_ppa(block)
    if bad:
        return ["the result's `ppa` object is malformed: " + "; ".join(bad)]
    if block.get("available") is False and _get(res, "stages", "ppa", "mode") != "require":
        return ["the PPA columns were not computed (" + str(block.get("reason"))[:200] + "): an "
                "official record needs `check.py --ppa require` (fetch the pinned liberty with "
                "`python3.12 score/ppa.py --fetch-liberty`); a record WITHOUT the columns comes "
                "from a result made with `--ppa off`"]
    return []


def _isint(v, least=0):
    return isinstance(v, int) and not isinstance(v, bool) and v >= least


def _zero(v):
    """`v` is the integer 0 (not False, not 0.0)."""
    return _isint(v) and v == 0


def clocked_acceptance_problems(res, task, postsynth="full"):
    """Why the clocked half of `res` does not entitle a submission to a record for `task`, a task of a CLOCKED_KINDS
    kind (the clocked record format, decided 2026-11-07); [] when it does. The clocked flow scored it
    (`stages.score.flow` "seq") with the clocked score (check.py `score_clocked`: CLOCKED_SCORE_KEYS), and
    `stages.postsynth.points` holds EVERY point of the task (`clocked_points`) once, each of the task's kind, in full
    mode (light only for a light record), with every seed of the task (`clocked_seeds`: seeds 0 to S-1, each with its
    cycles and the count its kind's check makes, CLOCKED_SEED_UNIT), 0 mismatches, its netlist's sha256 and its
    latency: the point's own `lat p` from the result's `latency_at` (F8, decided 2026-11-08: check.py has the kernel
    evaluate the proved latency function at every point; the scoring point's is the declared n), or the declared n at
    every point for a result without `latency_at` (an older checker); the stage's `netlist_sha256` is the scoring
    point's, the netlist the `ppa` block weighed."""
    p = []
    sc = res.get("score") if isinstance(res.get("score"), dict) else {}
    if _get(res, "stages", "score", "flow") != SEQ_FLOW:
        p.append(f"a {task.get('kind')} task is scored by the clocked flow (score/svgolf_seq.ys, ge_seq.json): the "
                 f"result's stages.score.flow is {_get(res, 'stages', 'score', 'flow')!r}, not 'seq'")
    if sc and not all(k in sc for k in CLOCKED_SCORE_KEYS):
        p.append(f"a {task.get('kind')} task's score is the clocked one (check.py `score_clocked`): the result's score "
                 f"lacks {[k for k in CLOCKED_SCORE_KEYS if k not in sc]}")
    ps = _get(res, "stages", "postsynth")
    pts = ps.get("points") if isinstance(ps, dict) else None
    if not (isinstance(pts, list) and pts and all(isinstance(x, dict) for x in pts)):
        return p + ["the clocked post-synthesis check did not pass: the result has no `stages.postsynth.points` (a "
                    "result of an older checker, or a run without scoring)"]
    want = [point_text(q) for q in clocked_points(task)]
    got = [x.get("point") for x in pts]
    missing = [w for w in want if w not in got]
    if missing:
        p.append(f"the clocked post-synthesis check did not run at every point of the task: {missing} missing (the "
                 f"task's points are {want})")
    extra = sorted({str(g) for g in got if g not in want})
    if extra:
        p.append(f"the clocked post-synthesis check ran at points the task does not list: {extra}")
    twice = sorted({str(g) for g in got if got.count(g) > 1})
    if twice:
        p.append(f"the clocked post-synthesis check lists the points {twice} more than once")
    seeds, unit = clocked_seeds(task), CLOCKED_SEED_UNIT.get(task.get("kind"))
    latency = res.get("latency")
    # F8 (decided 2026-11-08): a latency kind's every point is checked against its OWN latency, the kernel's `lat p`
    # (check.py `latency_at`, the scoring point's the declared n); a result without `latency_at` (an older checker)
    # used the declared n at every point
    lat_at = res.get("latency_at")
    if latency is not None and lat_at is not None:
        if not (isinstance(lat_at, dict) and sorted(lat_at) == sorted(want)
                and all(_isint(v, 1) for v in lat_at.values())):
            p.append(f"the result's latency_at {lat_at!r} does not give a latency for each clocked point {want}")
            lat_at = {}
        elif lat_at.get(point_text(scoring_point(task))) != latency:
            p.append(f"latency_at gives the scoring point {lat_at.get(point_text(scoring_point(task)))!r}, not the "
                     f"declared {latency!r}")
    for x in pts:
        at = f"stages.postsynth.points[{x.get('point')!r}]"
        if x.get("kind") != task.get("kind"):
            p.append(f"{at} is a check of the kind {x.get('kind')!r}, not the task's {task.get('kind')!r}")
        if not _zero(x.get("mismatches")) or x.get("report"):
            p.append(f"{at} did not pass: mismatches {x.get('mismatches')!r}")
        if x.get("mode") not in POSTSYNTH_MODES:
            p.append(f"{at}.mode {x.get('mode')!r} is neither 'light' nor 'full'")
        elif x["mode"] == "light" and postsynth != "light":
            p.append(f"{at} ran in LIGHT mode (local feedback): an official record needs the full check at every "
                     "point. Rerun check.py with --postsynth full, or record it as a light record with `add "
                     "--postsynth light`")
        if not SHA_RE.fullmatch(str(x.get("netlist_sha256", ""))):
            p.append(f"{at} has no netlist sha256")
        want_lat = latency if latency is None or lat_at is None else lat_at.get(x.get("point"))
        if x.get("latency") != want_lat:
            p.append(f"{at} checked the latency {x.get('latency')!r}, not the point's {want_lat!r}")
        ss = x.get("seeds")
        ran = ([s.get("seed") for s in ss] if isinstance(ss, list) and all(isinstance(s, dict) for s in ss)
               else None)
        if ran != list(range(seeds)):
            p.append(f"{at} did not run every seed of the task: seeds {ran if ran is not None else ss!r}, not the "
                     f"task's 0 to {seeds - 1}")
            continue
        for s in ss:
            if not _isint(s.get("cycles"), 1):
                p.append(f"{at} seed {s.get('seed')} does not record its cycles")
            if unit is not None and unit not in s:
                p.append(f"{at} seed {s.get('seed')} does not record its {unit}")
    if p:
        return p
    first = pts[got.index(point_text(scoring_point(task)))]       # the scoring point's check
    if ps.get("netlist_sha256") != first["netlist_sha256"]:
        p.append("stages.postsynth.netlist_sha256 is not the netlist checked at the scoring point")
    pb = res.get("ppa")
    if isinstance(pb, dict) and pb.get("available") is True and pb.get("netlist_sha256") != ps.get("netlist_sha256"):
        p.append("the `ppa` block weighed another netlist (ppa.netlist_sha256) than the one checked at the scoring "
                 "point (stages.postsynth.netlist_sha256)")
    if _isint(sc.get("cycles"), 1) and sc["cycles"] != (latency or 1):
        p.append(f"score.cycles {sc['cycles']} is not the declared latency {latency!r} (1 when none is declared)")
    return p


def clocked_postsynth_record(task, ps):
    """The `postsynth` of a clocked record, from the result's `stages.postsynth` (`clocked_acceptance_problems` passed
    it): `mode` ("light" if one point ran light, else "full"), `mismatches` (0), `netlist_sha256` (the scored netlist,
    the scoring point's) and `points`, in `clocked_points` order: each with `point` (check.py's name), `params`,
    `mode`, `mismatches`, `netlist_sha256`, `latency` and `seeds`, each seed's `seed` and `cycles`, its `segments`
    (react-family) or `transactions` (tx-family, stream-family) as a count (CLOCKED_SEED_UNIT; a seq-family seed counts
    neither), and `reset_cycles`, `salted`, `seed_sha256` and, since F5 (2026-11-07), the power-ups' draws
    `netlist_randseed` (Verilator's randSeed) and `lssv_start` (`zeros` or ls-sv's `seed:<k>`) where the check
    recorded them. Timings are not kept (they are not a fact about the design)."""
    order = {point_text(q): (k, q) for k, q in enumerate(clocked_points(task))}
    points = []
    for x in sorted(ps["points"], key=lambda x: order[x["point"]][0]):
        seeds = []
        for s in x["seeds"]:
            e = {"seed": s["seed"], "cycles": s["cycles"]}
            for k in ("reset_cycles", "salted", "seed_sha256", "netlist_randseed", "lssv_start"):
                if k in s:
                    e[k] = s[k]
            for k in ("segments", "transactions"):
                if k in s:
                    e[k] = len(s[k]) if isinstance(s[k], list) else s[k]
            seeds.append(e)
        points.append({"point": x["point"], "params": dict(order[x["point"]][1]), "mode": x["mode"],
                       "mismatches": x["mismatches"], "netlist_sha256": x["netlist_sha256"],
                       "latency": x.get("latency"), "seeds": seeds})
    return {"mode": "light" if any(q["mode"] == "light" for q in points) else "full", "mismatches": 0,
            "netlist_sha256": ps["netlist_sha256"], "points": points}


def build_record(task, res, *, player, assisted_by, notes, submitted_at, sv_name, sv_bytes,
                 lean_name, lean_bytes, environment, postsynth="full"):
    """The record of one accepted submission. Pure: everything it records is an
    argument. `task` is the task's task.json, `res` check.py's result JSON,
    `environment` {svgolf_revision, lean_toolchain, files} as `collect_environment`
    returns it. `postsynth` is the mode the record was asked for ("full", or
    "light" to allow a light record). Raises Refused (all problems at once) if the
    submission is not accepted or a human-supplied field is malformed."""
    problems = []
    try:
        player = normalize_player(player)
    except Refused as e:
        problems += e.problems
    try:
        assisted = normalize_assisted_by(assisted_by)
    except Refused as e:
        problems += e.problems
    try:
        notes = normalize_notes(notes)
    except Refused as e:
        problems += e.problems
    try:
        submitted_at = normalize_date(submitted_at)
    except Refused as e:
        problems += e.problems
    sv_sha, lean_sha = sha256_bytes(sv_bytes), sha256_bytes(lean_bytes)
    if postsynth not in POSTSYNTH_MODES:
        problems.append(f"postsynth {postsynth!r} is neither 'light' nor 'full'")
    problems += acceptance_problems(res, task, sv_sha, postsynth)
    try:
        lean_text = lean_bytes.decode("utf-8")
    except UnicodeDecodeError:
        lean_text = ""
        problems.append("the .lean file is not UTF-8")
    if problems:
        raise Refused(problems)

    st, sc = res["stages"], res["score"]
    imports = _get(st, "imports", "imports")
    if not isinstance(imports, list):
        imports = lean_imports(lean_text)
    ps, comp = st["postsynth"], st["comparator"]["result"]
    clocked = is_clocked_task(task)
    if clocked:
        # the Verilator of the clocked check: the scoring point's
        first = point_text(scoring_point(task))
        verilator = next(x.get("verilator") for x in ps["points"] if x["point"] == first)
    else:
        verilator = ps.get("verilator")
    rec = {
        "schema": SCHEMA,
        "task": task["name"],
        "player": player,
        "assisted_by": assisted,
        "submitted_at": submitted_at,
        "files": {"sv": {"name": os.path.basename(sv_name), "sha256": sv_sha},
                  "lean": {"name": os.path.basename(lean_name), "sha256": lean_sha}},
        "canonical_sha256": st["source"]["canonical_sha256"],
        "score": {
            "area_mge": sc["area_mge"],
            "area_ge": round(sc["area_mge"] / 1000, 3),
            "depth": sc["depth"],
            "num_gates": sc.get("num_gates", sum(sc["gates"].values())),
            "gates": dict(sorted(sc["gates"].items())),
            "top": _get(st, "score", "top", default=task.get("top")),
            "scoring_point": dict(sorted(sc["params"].items())),
            "rtlil_sha256": _get(st, "score", "rtlil_sha256"),
        },
        "checker": {
            "svgolf_revision": environment.get("svgolf_revision"),
            "lean_surfaces_revision": _get(st, "extract", "lean_surfaces"),
            "lean_toolchain": environment.get("lean_toolchain"),
            "yosys": _get(st, "score", "yosys_version"),
            "verilator": verilator,
            "extractor_sha256": _get(st, "extract", "extractor_sha256"),
            "canon_script_sha256": _get(st, "score", "canon_script_sha256"),
            "script_sha256": _get(st, "score", "script_sha256"),
            "ge_table_sha256": _get(st, "score", "ge_table_sha256"),
            "files": dict(sorted((environment.get("files") or {}).items())),
        },
        "proof": {
            "axioms": sorted(comp["axioms"]),
            "build_seconds": _get(st, "solution", "seconds"),
            "lines": lean_code_lines(lean_text),
            "imports": list(imports),
            "tactics": lean_tactics(lean_text),
            "uses_comb_view": any(m.startswith("LeanModels.Sv.CombView") for m in imports),
            "uses_comb_eq": any(m.startswith("LeanModels.Sv.CombEq") for m in imports),
        },
        "postsynth": (clocked_postsynth_record(task, ps) if clocked else
                      {"point": ps.get("point"), "vectors": ps["vectors"],
                       "mismatches": ps["mismatches"], "salted": bool(ps.get("salted")),
                       "seed": ps.get("seed"), "mode": record_mode(ps),
                       "full_vectors": ps.get("full_vectors", ps["vectors"])}),
        "notes": notes,
    }
    if res.get("ppa") is not None:
        rec[PPA_KEY] = copy.deepcopy(res["ppa"])
    if clocked:
        # a clocked result's ranked score (check.py `score_clocked`): validate_record holds it to the `ppa` block; and
        # the record names the flow of its kind (a combinational record names none: it stays as it was)
        rec["score"].update({k: sc[k] for k in CLOCKED_SCORE_KEYS + ("ffs",) if k in sc})
        rec["checker"]["flow"] = SEQ_FLOW
    if isinstance(environment.get("statement"), dict) and environment["statement"]:
        rec["checker"]["statement"] = dict(sorted(environment["statement"].items()))
    rec["record_hash"] = compute_record_hash(rec)
    bad = validate_record(rec)
    if bad:
        raise Refused(["the built record is invalid: " + "; ".join(bad)])
    return rec


# ---------------------------------------------------------------------------
# record validation (pure)
# ---------------------------------------------------------------------------

_TOP_KEYS = {"schema", "task", "player", "assisted_by", "submitted_at", "files",
             "canonical_sha256", "score", "checker", "proof", "postsynth", "notes",
             "record_hash"}
_OPTIONAL_KEYS = {PPA_KEY}      # additive: absent in every record made before the PPA columns


def validate_ppa(block):
    """Structural problems of a `ppa` object (a check result's, or a record's); [] if it is
    well-formed. Two shapes: `{"available": false, "reason": "..."}` (the pinned flow could not
    weigh the design, or the liberty was absent), or the columns of score/ppa.py with
    `available: true`. Internal arithmetic is checked (area in um^2 is area_e4um2 / 10^4, the
    histogram sums to the cell count); consistency with the record's own score is
    `ppa_score_problems`'s. Unknown extra keys are allowed (additive evolution is what
    `ppa_version` is for)."""
    if not isinstance(block, dict):
        return ["ppa must be an object"]
    avail = block.get("available")
    if avail is True and PPA_MAPPED_KEY in block:
        bad = validate_mapped(block[PPA_MAPPED_KEY])
        if bad:
            return bad
    if avail is False:
        extra = sorted(set(block) - {"available", "reason"})
        ok = isinstance(block.get("reason"), str) and block["reason"] and not extra
        return [] if ok else ["an unavailable ppa object is exactly {available: false, reason: "
                              "<non-empty text>}"]
    if avail is not True:
        return ["ppa.available must be true or false"]
    p = []

    def isint(v):
        return isinstance(v, int) and not isinstance(v, bool) and v >= 0

    for k in ("area_e4um2_sky130", "delay_ps_sky130", "unit_depth", "cells_sky130"):
        if not isint(block.get(k)):
            p.append(f"ppa.{k} must be a non-negative integer")
    for k in ("liberty_sha256", "ppa_pins_sha256", "ppa_script_sha256", "netlist_sha256"):
        if not (isinstance(block.get(k), str) and SHA_RE.fullmatch(block[k])):
            p.append(f"ppa.{k} must be a sha256 hex digest")
    if not (isinstance(block.get("ppa_version"), str) and block["ppa_version"]):
        p.append("ppa.ppa_version must be a non-empty string")
    if not isinstance(block.get("constants"), bool):
        p.append("ppa.constants must be a boolean")
    hist = block.get("cell_hist_sky130")
    if not (isinstance(hist, dict) and all(isinstance(k, str) and isint(v) for k, v in hist.items())):
        p.append("ppa.cell_hist_sky130 must map cell names to counts")
    elif isint(block.get("cells_sky130")) and sum(hist.values()) != block["cells_sky130"]:
        p.append("ppa.cells_sky130 is not the sum of ppa.cell_hist_sky130")
    if isint(block.get("area_e4um2_sky130")) and block.get("area_um2_sky130") != \
            block["area_e4um2_sky130"] / 10000:
        p.append("ppa.area_um2_sky130 is not area_e4um2_sky130 / 10000")
    return p


def validate_mapped(m):
    """Structural problems of a `ppa.mapped` object (flow A1'): `{"available": false, "reason": "..."}` or the columns of
    score/ppa.py's `mapped_columns` with `available: true`; [] if well-formed. Internal arithmetic is checked (area in um^2 is
    area_e4um2 / 10^4, the histogram sums to the cell count, the buffer and inverter counts are those of the histogram);
    consistency with the record's own score is `ppa_score_problems`'s. Unknown extra keys are allowed."""
    if not isinstance(m, dict):
        return ["ppa.mapped must be an object"]
    if m.get("available") is False:
        ok = isinstance(m.get("reason"), str) and m["reason"] and not (set(m) - {"available", "reason"})
        return [] if ok else ["an unavailable ppa.mapped is exactly {available: false, reason: <non-empty text>}"]
    if m.get("available") is not True:
        return ["ppa.mapped.available must be true or false"]
    p = []

    def isint(v):
        return isinstance(v, int) and not isinstance(v, bool) and v >= 0

    for k in ("area_e4um2_sky130_mapped_v1", "mapped_delay_sky130_v1", "mapped_cells_sky130_v1", "mapped_levels_sky130_v1",
              "mapped_buffers_sky130_v1", "mapped_inverters_sky130_v1"):
        if not isint(m.get(k)):
            p.append(f"ppa.mapped.{k} must be a non-negative integer")
    for k in ("liberty_sha256", "ppa_pins_sha256", "ppa_mapped_pins_sha256", "ppa_mapped_script_sha256",
              "ppa_script_sha256", "rtlil_sha256", "netlist_sha256"):
        if not (isinstance(m.get(k), str) and SHA_RE.fullmatch(m[k])):
            p.append(f"ppa.mapped.{k} must be a sha256 hex digest")
    for k in ("ppa_mapped_version", "yosys_version"):
        if not (isinstance(m.get(k), str) and m[k]):
            p.append(f"ppa.mapped.{k} must be a non-empty text")
    if not (m.get("abc_version") is None or isinstance(m.get("abc_version"), str)):
        p.append("ppa.mapped.abc_version must be a text or null")
    if not isinstance(m.get("constants"), bool):
        p.append("ppa.mapped.constants must be a boolean")
    hist = m.get("mapped_cell_hist_sky130_v1")
    if not (isinstance(hist, dict) and all(isinstance(k, str) and isint(v) for k, v in hist.items())):
        p.append("ppa.mapped.mapped_cell_hist_sky130_v1 must map cell names to counts")
    else:
        if isint(m.get("mapped_cells_sky130_v1")) and sum(hist.values()) != m["mapped_cells_sky130_v1"]:
            p.append("ppa.mapped.mapped_cells_sky130_v1 is not the sum of mapped_cell_hist_sky130_v1")
        bufs = sum(n for c, n in hist.items() if c.startswith(("buf_", "bufbuf_", "bufinv_")))
        invs = sum(n for c, n in hist.items() if c.startswith("inv_"))
        if (m.get("mapped_buffers_sky130_v1"), m.get("mapped_inverters_sky130_v1")) != (bufs, invs):
            p.append("ppa.mapped buffer and inverter counts are not those of the histogram")
    if isint(m.get("area_e4um2_sky130_mapped_v1")) and m.get("area_um2_sky130_mapped_v1") != \
            m["area_e4um2_sky130_mapped_v1"] / 10000:
        p.append("ppa.mapped.area_um2_sky130_mapped_v1 is not area_e4um2_sky130_mapped_v1 / 10000")
    eq = m.get("equivalence")
    if not (isinstance(eq, dict) and isint(eq.get("vectors")) and eq["vectors"] > 0):
        p.append("ppa.mapped.equivalence must record the number of vectors the mapped netlist was compared on")
    return p


def ppa_score_problems(rec):
    """The `ppa` columns of a record against the record's OWN score, which they must agree
    with exactly (the scorer's `ltp -noff` depth is the weighed netlist's unit depth; its gate
    count is the weighed cell count, plus the one tie cell when a constant is priced; under the
    buffering repair of sky130_a0_v2, `repair.cells_before` plus the repair's buffers and tie
    cells). [] when the record has no numeric `ppa` block."""
    b = rec.get(PPA_KEY)
    if not (isinstance(b, dict) and b.get("available") is True):
        return []
    p = []
    sc = rec.get("score", {})
    if b.get("unit_depth") != sc.get("depth"):
        p.append(f"ppa.unit_depth {b.get('unit_depth')!r} is not score.depth {sc.get('depth')!r}")
    rep = b.get("repair")
    if isinstance(rep, dict) and rep.get("method") == "buffer_trees_v1":
        # sky130_a0_v2 (buffering only): the scored gates, plus the repair's buffers and tie cells, nothing resized
        if rep.get("cells_before") != sc.get("num_gates"):
            p.append(f"ppa.repair.cells_before {rep.get('cells_before')!r} is not score.num_gates {sc.get('num_gates')!r}")
        want = sum(x for x in (rep.get("cells_before"), rep.get("buffers"), rep.get("tie_cells")) if isinstance(x, int))
        if b.get("cells_sky130") != want:
            p.append(f"ppa.cells_sky130 {b.get('cells_sky130')!r} is not repair.cells_before + buffers + tie_cells = {want}")
    else:
        want = sc.get("num_gates", 0) + (1 if b.get("constants") else 0)
        if b.get("cells_sky130") != want:
            p.append(f"ppa.cells_sky130 {b.get('cells_sky130')!r} is not score.num_gates"
                     + (" + 1 (the priced tie cell)" if b.get("constants") else "") + f" = {want}")
    m = b.get(PPA_MAPPED_KEY)
    if isinstance(m, dict) and m.get("available") is True and sc.get("rtlil_sha256") \
            and m.get("rtlil_sha256") != sc["rtlil_sha256"]:
        p.append("ppa.mapped.rtlil_sha256 is not the canonical RTLIL the score was computed from "
                 "(score.rtlil_sha256): the mapping did not read this design")
    return p


def validate_record(rec):
    """Structural problems of a record (types, shapes, internal consistency);
    [] if it is well-formed. Does not look at files or recompute the hash."""
    if not isinstance(rec, dict):
        return ["the record is not a JSON object"]
    p = []
    if rec.get("schema") != SCHEMA:
        p.append(f"schema {rec.get('schema')!r} is not {SCHEMA!r}")
    unknown = sorted(set(rec) - _TOP_KEYS - _OPTIONAL_KEYS)
    missing = sorted(_TOP_KEYS - set(rec))
    if unknown:
        p.append(f"unknown keys {unknown}")
    if missing:
        p.append(f"missing keys {missing}")
    if missing:
        return p

    def need(cond, msg):
        if not cond:
            p.append(msg)

    need(isinstance(rec["task"], str) and rec["task"], "task must be a non-empty string")
    need(isinstance(rec["player"], str) and PLAYER_RE.fullmatch(rec["player"]),
         "player is not a valid handle")
    need(isinstance(rec["assisted_by"], list)
         and all(isinstance(x, str) and x and len(x) <= MAX_ASSIST_LEN for x in rec["assisted_by"]),
         "assisted_by must be a list of non-empty strings")
    need(isinstance(rec["submitted_at"], str) and DATE_RE.fullmatch(rec["submitted_at"]),
         "submitted_at must be an ISO date")
    need(isinstance(rec["notes"], str), "notes must be a string")
    need(isinstance(rec["canonical_sha256"], str) and SHA_RE.fullmatch(rec["canonical_sha256"]),
         "canonical_sha256 must be a sha256 hex digest")
    need(isinstance(rec["record_hash"], str) and SHA_RE.fullmatch(rec["record_hash"]),
         "record_hash must be a sha256 hex digest")
    f = rec["files"]
    if isinstance(f, dict) and set(f) == {"sv", "lean"}:
        for k in ("sv", "lean"):
            e = f[k]
            need(isinstance(e, dict) and set(e) == {"name", "sha256"}
                 and isinstance(e["name"], str) and e["name"]
                 and isinstance(e["sha256"], str) and SHA_RE.fullmatch(e["sha256"]),
                 f"files.{k} must be {{name, sha256}}")
    else:
        p.append("files must be {sv, lean}")
    s = rec["score"]
    if isinstance(s, dict):
        ints = all(isinstance(s.get(k), int) and not isinstance(s.get(k), bool) and s[k] >= 0
                   for k in ("area_mge", "depth", "num_gates"))
        need(ints, "score.area_mge, depth and num_gates must be non-negative integers")
        need(isinstance(s.get("gates"), dict) and all(isinstance(v, int) and v >= 0
                                                       for v in s["gates"].values()),
             "score.gates must map gate types to counts")
        need(isinstance(s.get("scoring_point"), dict), "score.scoring_point must be an object")
        if ints:
            need(s.get("area_ge") == round(s["area_mge"] / 1000, 3),
                 "score.area_ge is not area_mge / 1000")
            if isinstance(s.get("gates"), dict):
                need(sum(s["gates"].values()) == s["num_gates"],
                     "score.num_gates is not the sum of score.gates")
    else:
        p.append("score must be an object")
    c = rec["checker"]
    if isinstance(c, dict):
        for k in ("canon_script_sha256", "script_sha256", "ge_table_sha256"):
            need(isinstance(c.get(k), str) and SHA_RE.fullmatch(c[k]),
                 f"checker.{k} must be a sha256 hex digest")
        need(isinstance(c.get("yosys"), str) and c["yosys"], "checker.yosys must be a string")
        need(isinstance(c.get("files"), dict), "checker.files must be an object")
        need(c.get("flow", SEQ_FLOW) == SEQ_FLOW,
             "checker.flow must be 'seq' (a clocked record) or absent (a combinational one)")
        st = c.get("statement")
        need(st is None or (isinstance(st, dict) and st and all(
            isinstance(f, str) and f.endswith(".lean") and isinstance(h, str) and SHA_RE.fullmatch(h)
            for f, h in st.items())),
             "checker.statement must map the trusted statement files (svgolf/-relative .lean paths) to their sha256, "
             "or be absent (a record made before 2026-11-07)")
    else:
        p.append("checker must be an object")
    clocked = record_flow(rec) == SEQ_FLOW
    pr = rec["proof"]
    if isinstance(pr, dict):
        need(isinstance(pr.get("axioms"), list) and pr["axioms"] == sorted(pr["axioms"]),
             "proof.axioms must be a sorted list")
        need(isinstance(pr.get("lines"), int) and pr["lines"] >= 0,
             "proof.lines must be a non-negative integer")
        need(isinstance(pr.get("imports"), list), "proof.imports must be a list")
        need(isinstance(pr.get("tactics"), list), "proof.tactics must be a list")
        need(isinstance(pr.get("uses_comb_view"), bool) and isinstance(pr.get("uses_comb_eq"), bool),
             "proof.uses_comb_view / uses_comb_eq must be booleans")
    else:
        p.append("proof must be an object")
    ps = rec["postsynth"]
    if clocked:
        p += clocked_postsynth_problems(rec)
    else:
        need(isinstance(ps, dict) and ps.get("mismatches") == 0 and isinstance(ps.get("vectors"), int),
             "postsynth must record vectors and mismatches 0")
    if isinstance(ps, dict) and not clocked:
        need(record_mode(ps) in POSTSYNTH_MODES, "postsynth.mode must be 'light' or 'full'")
        need(ps.get("full_vectors") is None or (isinstance(ps["full_vectors"], int)
                                                and not isinstance(ps["full_vectors"], bool)
                                                and ps["full_vectors"] >= 0),
             "postsynth.full_vectors must be a non-negative integer")
        need("points" not in ps, "postsynth.points is the post-synthesis check of a clocked record (checker.flow "
             "'seq')")
    if PPA_KEY in rec:
        bad = validate_ppa(rec[PPA_KEY])
        p += bad
        if not bad:
            p += ppa_score_problems(rec)
    if clocked or (isinstance(s, dict) and any(k in s for k in CLOCKED_SCORE_KEYS)):
        p += clocked_score_problems(rec)
        need(clocked, "a clocked score (score.time_ps = cycles x period_ps) is the score of a record of the clocked "
             "flow (checker.flow 'seq')")
    return p


_CLOCKED_PS_KEYS = {"mode", "mismatches", "netlist_sha256", "points"}
_CLOCKED_POINT_KEYS = {"point", "params", "mode", "mismatches", "netlist_sha256", "latency", "seeds"}
_CLOCKED_SEED_KEYS = {"seed", "cycles", "reset_cycles", "salted", "seed_sha256", "segments", "transactions",
                      "netlist_randseed", "lssv_start"}
LSSV_START_RE = re.compile(r"zeros|seed:\d{1,20}")


def clocked_postsynth_problems(rec):
    """Structural problems of a clocked record's `postsynth` (`clocked_postsynth_record`'s shape), and its agreement
    with the record's own score and `ppa` block: the points are distinct, each named after its params, passed (0
    mismatches) with its seeds 0 to n-1; the top-level mode is "light" exactly when a point ran light; one point is the
    scoring point, and its netlist is `postsynth.netlist_sha256`, the netlist the `ppa` block weighed; the scoring
    point used the latency `score.cycles` counts (1 when none is declared), and the points declare a latency all or
    none (F8, 2026-11-08: another point's is its own `lat p`, which only the kernel gives: acceptance holds it to the
    result's `latency_at`, `verify --full` to a fresh check's). Whether the points and seeds are the TASK's is
    acceptance (`clocked_acceptance_problems`), which needs the task.json. [] when well-formed."""
    ps = rec.get("postsynth")
    if not isinstance(ps, dict):
        return ["postsynth must be an object"]
    p = []
    extra = sorted(set(ps) - _CLOCKED_PS_KEYS)
    if extra:
        p.append(f"a clocked record's postsynth has the unknown keys {extra}")
    if not _zero(ps.get("mismatches")):
        p.append("postsynth.mismatches must be 0")
    if ps.get("mode") not in POSTSYNTH_MODES:
        p.append("postsynth.mode must be 'light' or 'full'")
    if not SHA_RE.fullmatch(str(ps.get("netlist_sha256", ""))):
        p.append("postsynth.netlist_sha256 must be a sha256 hex digest")
    pts = ps.get("points")
    if not (isinstance(pts, list) and pts and all(isinstance(x, dict) for x in pts)):
        return p + ["a clocked record's postsynth.points must be a non-empty list of points"]
    for k, x in enumerate(pts):
        at = f"postsynth.points[{k}]"
        if set(x) != _CLOCKED_POINT_KEYS:
            p.append(f"{at} must have exactly the keys {sorted(_CLOCKED_POINT_KEYS)}")
            continue
        params = x["params"]
        if not (isinstance(params, dict) and all(isinstance(n, str) and isinstance(v, int) and not isinstance(v, bool)
                                                 for n, v in params.items())):
            p.append(f"{at}.params must map parameter names to integers")
            continue
        # the same name=value pairs in any order: check.py names a point in the task's parameter order (N, W, AccW),
        # and a stored record's params come back in sorted key order (the file is written with sorted keys)
        if sorted(str(x["point"]).split(",")) != sorted(point_text(params).split(",")):
            p.append(f"{at}.point {x['point']!r} is not the name of its params {params}")
        if x["mode"] not in POSTSYNTH_MODES:
            p.append(f"{at}.mode must be 'light' or 'full'")
        if not _zero(x["mismatches"]):
            p.append(f"{at}.mismatches must be 0")
        if not SHA_RE.fullmatch(str(x["netlist_sha256"])):
            p.append(f"{at}.netlist_sha256 must be a sha256 hex digest")
        if not (x["latency"] is None or _isint(x["latency"], 1)):
            p.append(f"{at}.latency must be a positive integer or null")
        seeds = x["seeds"]
        if not (isinstance(seeds, list) and seeds and all(isinstance(s, dict) for s in seeds)):
            p.append(f"{at}.seeds must be a non-empty list of seeds")
            continue
        if [s.get("seed") for s in seeds] != list(range(len(seeds))):
            p.append(f"{at}.seeds must be the seeds 0 to {len(seeds) - 1}, in order")
        for s in seeds:
            sat = f"{at}.seeds[{s.get('seed')!r}]"
            extra = sorted(set(s) - _CLOCKED_SEED_KEYS)
            if extra:
                p.append(f"{sat} has the unknown keys {extra}")
            if not _isint(s.get("cycles"), 1):
                p.append(f"{sat}.cycles must be a positive integer")
            counts = [c for c in ("segments", "transactions") if c in s]
            if len(counts) > 1 or (counts and not _isint(s[counts[0]])):
                p.append(f"{sat} counts at most one of segments, transactions (a non-negative integer)")
            if "reset_cycles" in s and not _isint(s["reset_cycles"]):
                p.append(f"{sat}.reset_cycles must be a non-negative integer")
            if "salted" in s and not isinstance(s["salted"], bool):
                p.append(f"{sat}.salted must be a boolean")
            if "seed_sha256" in s and not SHA_RE.fullmatch(str(s["seed_sha256"])):
                p.append(f"{sat}.seed_sha256 must be a sha256 hex digest")
            if "netlist_randseed" in s and not (_isint(s["netlist_randseed"], 1) and s["netlist_randseed"] < 2 ** 31):
                p.append(f"{sat}.netlist_randseed must be an integer in 1 .. 2^31 - 1 (Verilator's randSeed)")
            if "lssv_start" in s and not (isinstance(s["lssv_start"], str) and LSSV_START_RE.fullmatch(s["lssv_start"])):
                p.append(f"{sat}.lssv_start must be `zeros` or `seed:<k>` (ls-sv's power-up)")
    if p:
        return p
    names = [x["point"] for x in pts]
    if len(set(names)) != len(names):
        p.append(f"postsynth.points lists a point twice: {names}")
    if ps["mode"] != ("light" if any(x["mode"] == "light" for x in pts) else "full"):
        p.append("postsynth.mode must be 'light' exactly when one of its points ran light")
    sc = rec.get("score") if isinstance(rec.get("score"), dict) else {}
    at_sp = [x for x in pts if x["params"] == sc.get("scoring_point")]
    if not at_sp:
        p.append("postsynth.points has no check at the scoring point (score.scoring_point)")
    elif at_sp[0]["netlist_sha256"] != ps["netlist_sha256"]:
        p.append("postsynth.netlist_sha256 is not the netlist checked at the scoring point")
    b = rec.get(PPA_KEY)
    if isinstance(b, dict) and b.get("available") is True and b.get("netlist_sha256") != ps["netlist_sha256"]:
        p.append("ppa.netlist_sha256 is not postsynth.netlist_sha256: the sky130 columns weighed another netlist than "
                 "the one checked at the scoring point")
    if _isint(sc.get("cycles"), 1):
        # F8 (2026-11-08): the scoring point's latency is the score's cycles; another point's is its own `lat p`
        off = [x["point"] for x in pts if x["params"] == sc.get("scoring_point") and (x["latency"] or 1) != sc["cycles"]]
        if off:
            p.append(f"score.cycles {sc['cycles']} is not the latency the check used at {off} (1 when none is "
                     "declared)")
    if len({x["latency"] is None for x in pts}) > 1:
        p.append("postsynth.points declare a latency at some points and none at others: "
                 + ", ".join(f"{x['point']}: {x['latency']!r}" for x in pts))
    return p


# a clocked check result's ranked score (check.py `score_clocked`, C7): the sky130 area with the flops, and
# time_ps = cycles x period_ps, the register-to-register period of the `ppa` block
CLOCKED_SCORE_KEYS = ("area_um2", "period_ps", "cycles", "time_ps")


def clocked_score_problems(rec):
    """A clocked record's `score.area_um2`, `period_ps`, `cycles` and `time_ps` (the time the board ranks)
    against its own `ppa` block, which they must agree with exactly: the area is the block's `area_um2_sky130`,
    the period its `delay_ps_sky130` and the time cycles x period. [] when they agree."""
    s, b = rec.get("score") or {}, rec.get(PPA_KEY)
    if not all(k in s for k in CLOCKED_SCORE_KEYS):
        return [f"a clocked score has all of {', '.join(CLOCKED_SCORE_KEYS)} (score has "
                f"{', '.join(k for k in CLOCKED_SCORE_KEYS if k in s)})"]
    if not (isinstance(b, dict) and b.get("available") is True):
        return ["a clocked score is the sky130 one: the record needs its numeric `ppa` block"]
    p = []
    for k in ("period_ps", "cycles", "time_ps"):
        if not (isinstance(s[k], int) and not isinstance(s[k], bool) and s[k] >= (1 if k == "cycles" else 0)):
            p.append(f"score.{k} must be a{' positive' if k == 'cycles' else ' non-negative'} integer")
    if p:
        return p
    if s["period_ps"] != b.get("delay_ps_sky130"):
        p.append(f"score.period_ps {s['period_ps']} is not ppa.delay_ps_sky130 {b.get('delay_ps_sky130')!r}")
    if s["time_ps"] != s["cycles"] * s["period_ps"]:
        p.append(f"score.time_ps {s['time_ps']} is not cycles x period_ps = {s['cycles'] * s['period_ps']}")
    if s["area_um2"] != b.get("area_um2_sky130"):
        p.append(f"score.area_um2 {s['area_um2']!r} is not ppa.area_um2_sky130 {b.get('area_um2_sky130')!r}")
    return p


# ---------------------------------------------------------------------------
# ranking: area x time, the board; the Pareto frontier and layers (pure)
# ---------------------------------------------------------------------------

# The ranked axes (decided 11/03: sky130 A0' is the ranked metric), the two factors of the ONE ranked number,
# area x time (decided 2026-11-05; `combined.py`): the board orders by their product (`score_key`), and their
# Pareto frontier and layers are an exploration view. Both "lower is better", both exact integers: the A0'
# area in 1e-4 um^2 (`ppa.area_e4um2_sky130`) and the time in ps, which is the critical-path delay of a
# combinational design (`ppa.delay_ps_sky130`) and cycles x the register-to-register period of a clocked
# one (`score.time_ps`, check.py's clocked score). Area in GE (`score.area_mge`) and depth (`score.depth`)
# are extra columns; they rank nothing.
RANKED_AXES = ("area_um2_sky130", "time_ps")
RANKED_BY = "area_x_time"


def ranked_columns(rec, pdk=DEFAULT_PDK, asap7=None):
    """{area_e4um2, time_ps, cycles, period_ps} of a record's ranked score, or None if it has no numeric
    `ppa` block (a record made before the columns, or of a design the pinned flow could not weigh).
    `cycles` and `period_ps` are None for a combinational record. With `pdk` "asap7": {area_e5um2, time_ps, cycles,
    period_ps} from the record's entry in `asap7` (the task's leaderboard/asap7/<task>.json, `load_asap7`), or None
    without one (`asap7_columns`)."""
    if pdk == "asap7":
        return asap7_columns(rec, asap7)
    b = rec.get(PPA_KEY)
    if not (isinstance(b, dict) and b.get("available") is True):
        return None
    s = rec.get("score") or {}
    if "time_ps" in s:          # a clocked record: cycles x period (validate_record checks it against the block)
        return {"area_e4um2": b.get("area_e4um2_sky130"), "time_ps": s["time_ps"], "cycles": s.get("cycles"),
                "period_ps": s.get("period_ps")}
    return {"area_e4um2": b.get("area_e4um2_sky130"), "time_ps": b.get("delay_ps_sky130"), "cycles": None,
            "period_ps": None}


def row_of(rec, pdk=DEFAULT_PDK, asap7=None):
    """The flat row the ranking works on: the ranked number (`exact`, area x time in 1e-4 um^2 x ps, and
    `um2ns`, the same in the display unit um^2 x ns; `combined.of_record`), its two factors (`area_e4um2`,
    `time_ps`), all None without sky130 columns, and the extra columns (`area_mge`, `depth`, ...). With `pdk` "asap7"
    (the ASAP7 view; `asap7` the task's table, `load_asap7`): the ASAP7 factors instead, `area_e5um2` (1e-5 um^2, the
    library's own unit) in place of `area_e4um2`, `exact` in 1e-5 um^2 x ps, and `pdk: "asap7"` (`row_area`)."""
    if pdk == "asap7":
        ranked = asap7_columns(rec, asap7)
        cols = ranked or {"area_e5um2": None, "time_ps": None, "cycles": None, "period_ps": None}
        exact = combined.exact(cols["area_e5um2"], cols["time_ps"]) if ranked else None
        um2ns = combined.um2ns(exact, "asap7")
        cols = dict(cols, pdk="asap7")
    else:
        ranked = ranked_columns(rec)
        cols = ranked or {"area_e4um2": None, "time_ps": None, "cycles": None, "period_ps": None}
        exact = combined.of_record(rec) if ranked else None
        um2ns = combined.um2ns(exact)
    return {"record_hash": rec["record_hash"], "task": rec["task"], "player": rec["player"],
            "assisted_by": list(rec["assisted_by"]), "exact": exact, "um2ns": um2ns, **cols,
            "area_mge": rec["score"]["area_mge"], "depth": rec["score"]["depth"],
            "proof_lines": rec["proof"]["lines"], "submitted_at": rec["submitted_at"],
            "postsynth": record_mode(rec["postsynth"])}


def row_pdk(r):
    """The library a row's ranked columns are of: "asap7" for a row of the ASAP7 view, else sky130."""
    return r.get("pdk") or DEFAULT_PDK


def row_area(r):
    """A row's area in its library's integer unit: `area_e4um2` (sky130) or `area_e5um2` (asap7)."""
    return r.get("area_e5um2") if row_pdk(r) == "asap7" else r.get("area_e4um2")


def has_ranked_columns(r):
    """A row carries both ranked numbers (a record without sky130 columns does not: it is not ranked)."""
    return all(isinstance(v, int) and not isinstance(v, bool) for v in (row_area(r), r.get("time_ps")))


def score_key(r):
    """The board's order (decided 2026-11-05: area x time is the one ranked number), the site's
    (site/build.py `score_key`): area x time (`exact`), then area in GE, then depth, then the earlier
    date first, then record hash, so equal scores are ordered the same way on every machine and on the
    site. A row without the ranked number sorts after every row with it."""
    return (r["exact"] is None, r["exact"] or 0, r["area_mge"], r["depth"], r["submitted_at"], r["record_hash"])


def row_key(r):
    """The order of the Pareto views (exploration; the board orders by `score_key`): sky130 area, then
    time, then the earlier date first (on a tie in both the earlier record stands), then player, then
    record hash (so equal scores are ordered the same way on every machine). A row
    without the sky130 columns sorts after every row with them, by area in GE then
    depth."""
    if not has_ranked_columns(r):
        return (1, r["area_mge"], r["depth"], r["submitted_at"], r["player"], r["record_hash"])
    return (0, row_area(r), r["time_ps"], r["submitted_at"], r["player"], r["record_hash"])


def dominates(a, b):
    """`a` beats `b`: no worse on both ranked axes (sky130 area, time; the ASAP7 view's on its rows) and strictly
    better on one. Equal scores do not dominate each other (ties are kept)."""
    aa, ba = row_area(a), row_area(b)
    return (aa <= ba and a["time_ps"] <= b["time_ps"]
            and (aa < ba or a["time_ps"] < b["time_ps"]))


def pareto_layers(rows):
    """Non-dominated sorting (exploration: the board ranks by area x time): layer 1 is the Pareto
    frontier, layer 2 the frontier of the rest, and so on. Each layer is in `row_key` order. Every
    row carries the ranked columns (`has_ranked_columns`)."""
    remaining, layers = sorted(rows, key=row_key), []
    while remaining:
        front = [r for r in remaining if not any(dominates(o, r) for o in remaining)]
        assert front, "dominance must be a strict partial order"
        layers.append(front)
        gone = {id(r) for r in front}
        remaining = [r for r in remaining if id(r) not in gone]
    return layers


def pareto(rows):
    """The (sky130 area, time) Pareto frontier of `rows`: non-dominated rows,
    ties kept, in `row_key` order."""
    layers = pareto_layers(rows)
    return layers[0] if layers else []


def flow_of(rec):
    """The flow a record was scored under: the flow's name (`record_flow`: "comb" or "seq"), Yosys's version line
    and the hashes of canon.ys and of the flow's script and GE table (FLOW_FILES)."""
    c = rec["checker"]
    return {"flow": record_flow(rec), "yosys": c.get("yosys"), "canon_script_sha256": c.get("canon_script_sha256"),
            "script_sha256": c.get("script_sha256"), "ge_table_sha256": c.get("ge_table_sha256")}


def kind_flow_mismatch(rec, task):
    """Why `rec` is not of the flow of `task`'s kind (a combinational record on a clocked task's board, or the
    reverse: a task whose kind changed), or None. A record is compared only with the current flow of its own kind."""
    want, got = task_flow(task), record_flow(rec)
    if got == want:
        return None
    return (f"scored under the {got} flow, and a {task.get('kind') or 'combinational'} task is scored under the "
            f"{want} flow ({', '.join(FLOW_FILES[want])})")


def flow_mismatch(rec_flow, flow):
    """The keys in which a record's flow differs from `flow` (the current one);
    keys `flow` leaves None are not compared."""
    return sorted(k for k, v in flow.items() if v is not None and rec_flow.get(k) != v)


def _competition_ranks(rows):
    """The ranks of `rows` (in `score_key` order) by area x time, equal scores sharing a rank (1, 1, 3, ...),
    as on the site."""
    ranks, prev, rank = [], None, 0
    for i, r in enumerate(rows):
        if r["exact"] != prev:
            rank, prev = i + 1, r["exact"]
        ranks.append(rank)
    return ranks


def unranked_reason(rec, task, *, flow=None, identity=None, input_drive=None, statement=None, pdk=DEFAULT_PDK,
                    asap7=None, asap7_identity=None):
    """Why `rec` is not ranked on `task`'s board, or None if it is. Pure. In order: scored at another
    point; a LIGHT post-synthesis check (incomplete: never ranked); scored under another flow than the one of the
    task's kind (`kind_flow_mismatch`); checked under another flow than `flow` (given: the current flow of the task's
    kind, `current_flow(svgolf, task_flow(task))`); no sky130 columns (a record made before them: not
    ranked until it is backfilled, i.e. checked again) or columns that were not computed; columns of
    another `ppa_version`/liberty/pins than `identity` (given); weighed under another input drive than
    the task's `input_drive` (given); checked under another trusted statement than `statement` (given: the task's
    `current_statement`), or before records named theirs (`statement_mismatch`). The ASAP7 view (`pdk` "asap7"): the
    same up to the flow, then the ASAP7 columns instead of the sky130 ones (`asap7_mismatch` against `asap7`, the
    task's table, and `asap7_identity`, `asap7_identity()`; `identity` and `input_drive` are not used)."""
    point = scoring_point(task)
    if rec["score"]["scoring_point"] != point:
        return f"scored at {rec['score']['scoring_point']}, not at {point}"
    if statement is not None and statement_mismatch(rec, statement):
        return statement_mismatch(rec, statement)
    if record_mode(rec.get("postsynth")) == "light":
        return ("its post-synthesis check ran LIGHT (a subset of the vectors): an incomplete check, which never "
                "ranks (a light record is for local use)")
    if kind_flow_mismatch(rec, task):
        return kind_flow_mismatch(rec, task)
    if flow is not None and flow_mismatch(flow_of(rec), flow):
        return "checked under another flow (" + ", ".join(flow_mismatch(flow_of(rec), flow)) + " differ)"
    if pdk == "asap7":
        return asap7_mismatch(rec, task, asap7, identity=asap7_identity, flow=flow)
    b = rec.get(PPA_KEY)
    if b is None:
        return ("no sky130 columns (a record made before them): not ranked until it is backfilled "
                "(checked again, which records them)")
    if not (isinstance(b, dict) and b.get("available") is True):
        return "the sky130 columns were not computed: " + str((b or {}).get("reason", "?"))[:120]
    row = row_of(rec)
    if not has_ranked_columns(row) or row["exact"] is None:
        return "the sky130 columns lack a ranked number"
    if identity is not None and any(b.get(k) != identity.get(k) for k in PPA_IDENTITY):
        return ("sky130 columns computed under another version ("
                + ", ".join(k for k in PPA_IDENTITY if b.get(k) != identity.get(k)) + " differ)")
    return ppa_drive_mismatch(b, input_drive)


def build_board(task, records, *, flow=None, unassisted=False, identity=None, input_drive=None, statement=None,
                pdk=DEFAULT_PDK, asap7=None, asap7_identity=None):
    """The board of one task, ranked by area x time (decided 2026-11-05: the one ranked number,
    `combined.py`; the product of RANKED_AXES, the sky130 A0' area and time). With `pdk` "asap7" (the ASAP7 view,
    decided 2026-11-09): the same board on the ASAP7 columns (`asap7`, the task's table, `load_asap7`; `asap7_identity`,
    `asap7_identity()`), its rows carrying `area_e5um2` (`row_of`), its `ranked_axes` ASAP7_RANKED_AXES. `records` are
    its records (others are ignored); `flow`, if given, is the current pinned flow OF THE TASK'S KIND
    (`current_flow(svgolf, task_flow(task))`: {flow, yosys, canon_script_sha256, script_sha256,
    ge_table_sha256}; a key it lacks is not compared); `identity` (`ppa_identity()`) and
    `input_drive` (`ppa_setup_now(task)["input_drive"]`), if given, are what the sky130 columns must
    have been computed under. A record that is not comparable (`unranked_reason`: another point, flow,
    PPA identity or input drive, or no sky130 columns) is listed as `unranked` with the reason instead
    of ranked. With `unassisted`, only records with an empty `assisted_by` are considered.

    `ranking` is the board: the ranked rows in `score_key` order, each with its `rank` (equal area x
    time shares a rank: 1, 1, 3, as on the site) and its `layer`, the Pareto layer of (area, time) it is
    on (exploration: layer 1 is the frontier, 2 the frontier of the rest, ...). `frontier` and
    `dominated` are the same rows by layer (layer 1, then the rest by layer; `row_key` order within one),
    the exploration view `pareto` prints."""
    point = scoring_point(task)
    budget = effective_depth_budget(task)
    ranked, unranked = [], []
    for rec in sorted((r for r in records if r["task"] == task["name"]),
                      key=lambda r: score_key(row_of(r, pdk, asap7))):
        if unassisted and rec["assisted_by"]:
            continue
        row = row_of(rec, pdk, asap7)
        why = unranked_reason(rec, task, flow=flow, identity=identity, input_drive=input_drive, statement=statement,
                              pdk=pdk, asap7=asap7, asap7_identity=asap7_identity)
        if why:
            unranked.append(dict(row, reason=why))
        else:
            ranked.append(row)
    layers = pareto_layers(ranked)
    for k, layer in enumerate(layers, 1):
        for r in layer:
            r["layer"] = k
    ranking = sorted(ranked, key=score_key)
    for r, k in zip(ranking, _competition_ranks(ranking)):
        r["rank"] = k
        r["over_budget"] = budget is not None and r["depth"] > budget
    a7 = pdk == "asap7"
    board = {"task": task["name"], "title": task.get("title", ""), "scoring_point": point, "pdk": pdk,
             "ranked_by": RANKED_BY, "ranked_axes": list(ASAP7_RANKED_AXES if a7 else RANKED_AXES),
             "unit": combined.UNIT_ASCII,
             "depth_budget": budget, "flow_checked": flow is not None,
             "ppa_identity": asap7_identity if a7 else identity,
             "input_drive": ((asap7 or {}).get("identity") or {}).get("input_drive") if a7 else input_drive,
             "statement_checked": statement is not None,
             "ranking": [dict(r) for r in ranking],
             "frontier": [dict(r) for r in (layers[0] if layers else [])],
             "dominated": [dict(r) for layer in layers[1:] for r in layer],
             "budget_ranking": None, "unranked": unranked,
             "unassisted_only": bool(unassisted)}
    if budget is not None:
        within = [r for r in ranking if not r["over_budget"]]
        over = [r for r in ranking if r["over_budget"]]
        board["budget_ranking"] = (
            [dict(r, rank=k) for r, k in zip(within, _competition_ranks(within))]
            + [dict(r, rank=None) for r in over])
    return board


def par_of(task, records, *, flow=None, identity=None, input_drive=None, names=None,
           reference_player=REFERENCE_PLAYER, statement=None, pdk=DEFAULT_PDK, asap7=None, asap7_identity=None):
    """PAR of `task`, the bar to beat: among the reference player's records (the proved references,
    `seed-references`) that rank under `flow`, `identity` and `input_drive` (`unranked_reason`, as on the
    board), the one with the best area x time (leaderboard/combined.py: the ONE ranked number); None when
    there is none. Pure. A tie of the exact product goes to the design listed first among task.json's
    references (`names`: design sha256 -> (index, stem), `reference_names`; a design not listed comes after
    them), then to `row_key`. Returns the record's row plus `name` (the reference's stem, else the stored
    .sv's name without `.sv`), `exact` (in 1e-4 um^2 x ps) and `um2ns` (the display unit). With `pdk` "asap7": par
    of the ASAP7 view, by the ASAP7 product (`exact` in 1e-5 um^2 x ps; `unranked_reason`'s ASAP7 rule). Only a
    design task.json lists counts (decided 2026-11-12): a record of the reference player whose design is not in
    `names` is never par, and without `names` there is none."""
    names = names or {}
    best = None
    for rec in records:
        if rec.get("task") != task["name"] or rec.get("player") != reference_player:
            continue
        if _get(rec, "files", "sv", "sha256") not in names:
            continue
        if unranked_reason(rec, task, flow=flow, identity=identity, input_drive=input_drive, statement=statement,
                           pdk=pdk, asap7=asap7, asap7_identity=asap7_identity):
            continue
        row = row_of(rec, pdk, asap7)
        exact = row["exact"]
        if exact is None:
            continue
        idx, stem = names[rec["files"]["sv"]["sha256"]]
        key = (exact, idx, row_key(row))
        if best is None or key < best[0]:
            name = stem
            best = (key, dict(row, name=name, exact=exact, um2ns=row["um2ns"]))
    return best[1] if best else None


def fmt_par(par):
    """A par row as one line of text: '`mul_tree_h`: 8563.2000 um^2 x 5992 ps = 51311.23 um2*ns (record
    `0123456789ab`)'."""
    return (f"`{par['name']}`: {fmt_area(par)} um^2 x {fmt_time(par)} ps = {fmt_adp(par)} "
            f"{combined.UNIT_ASCII} (record `{par['record_hash'][:12]}`)")


# ---------------------------------------------------------------------------
# rendering (pure)
# ---------------------------------------------------------------------------

def fmt_ge(mge):
    """Milli-GE as exact decimal GE text: 112000 -> '112.000'."""
    sign, mge = ("-", -mge) if mge < 0 else ("", mge)
    return f"{sign}{mge // 1000}.{mge % 1000:03d}"


def md_escape(s):
    """Free text safe inside a Markdown table cell."""
    s = " ".join(s.split())
    for ch in "\\|`*_<>[]":
        s = s.replace(ch, "\\" + ch)
    return s


LIGHT_NOTE = ("Rows marked `light` were checked with the light post-synthesis check (a subset "
              "of the vectors, local feedback): an incomplete check, which never ranks; the others with the "
              "full check.")


def _record_cell(row):
    """The record column: the hash prefix, and `light` after it for a record
    whose post-synthesis check ran in light mode."""
    return f"`{row['record_hash'][:12]}`" + (" light" if row.get("postsynth") == "light" else "")


def _has_light(board):
    rows = board["ranking"] + (board["budget_ranking"] or []) + board["unranked"]
    return any(r.get("postsynth") == "light" for r in rows)


def _assist_cell(row):
    return md_escape("; ".join(row["assisted_by"])) if row["assisted_by"] else "none"


def _md_table(header, aligns, rows):
    out = ["| " + " | ".join(header) + " |",
           "|" + "|".join({"l": "---", "r": "--:"}[a] for a in aligns) + "|"]
    out += ["| " + " | ".join(r) + " |" for r in rows]
    return out


def fmt_um2(e4):
    """1e-4 um^2 as exact decimal um^2 text ('460.4416'); '-' for None."""
    return "-" if e4 is None else _fmt_e4(e4)


def fmt_um2_e5(e5):
    """1e-5 um^2 (the ASAP7 columns' unit) as exact decimal um^2 text ('6.99840'); '-' for None."""
    return "-" if e5 is None else f"{e5 // 100000}.{e5 % 100000:05d}"


def fmt_area(r):
    """A row's area as exact decimal um^2 text, in its library's unit (`row_area`); '-' without it."""
    return fmt_um2_e5(r.get("area_e5um2")) if row_pdk(r) == "asap7" else fmt_um2(r.get("area_e4um2"))


def fmt_time(r):
    """A row's ranked time as text: the delay in ps ('2611'), or for a clocked record the time and how it is
    made ('42784 (4 x 10696)'); '-' without sky130 columns."""
    if r.get("time_ps") is None:
        return "-"
    if r.get("cycles") is not None:
        return f"{r['time_ps']} ({r['cycles']} x {r['period_ps']})"
    return str(r["time_ps"])


def fmt_adp(r):
    """A row's ranked number, area x time in um^2 x ns, as text ('12022.21', as `fmt_par` and check.py's
    headline print it); '-' without it."""
    if r.get("exact") is None:
        return "-"
    v = combined.um2ns(r["exact"], row_pdk(r))
    return f"{v:.2f}" if row_pdk(r) != "asap7" else f"{v:.4f}"     # ASAP7 scores are ~250x smaller: 4 decimals


ADP_HEAD = f"area x time ({combined.UNIT_ASCII})"
LAYER_NOTE = ("`layer` is the entry's Pareto layer of (area, time), an exploration column like area in GE and "
              "depth: layer 1 is the frontier (no other entry is at least as good on both and better on one), "
              "layer 2 the frontier of the rest, and so on. It ranks nothing.")


def render_markdown(board, level=2):
    """The board of one task as Markdown (headings at `level`)."""
    h = "#" * level
    budget = board["depth_budget"]
    lines = [f"{h} `{board['task']}`" + (f" - {md_escape(board['title'])}" if board["title"] else ""),
             ""]
    point = ", ".join(f"{k} = {v}" for k, v in board["scoring_point"].items()) or "fixed size"
    lines.append(f"Scoring point: {point}. Depth budget: "
                 + (f"depth <= {budget}" if budget is not None else "none")
                 + (f". Input drive: `{board['input_drive']}`" if board.get("input_drive") else "")
                 + (". Unassisted entries only" if board["unassisted_only"] else "") + ".")
    lines.append("")
    if board.get("pdk") == "asap7":
        lines += [ASAP7_BOARD_NOTE, ""]
    if "par" in board:          # (`_boards` sets it; a board built by `build_board` alone has no par line)
        lines += [par_line(board["par"]), ""]
    if not board["ranking"]:
        lines += ["No ranked records.", ""]
    else:
        header = ["#", "player", "assisted by", ADP_HEAD, "area (um^2)", "time (ps)", "layer", "area (GE)",
                  "depth", "proof lines", "date", "record"]
        aligns = ["r", "l", "l", "r", "r", "r", "r", "r", "r", "r", "l", "l"]
        if budget is not None:
            header.insert(9, "budget")
            aligns.insert(9, "l")
        trs = []
        for r in board["ranking"]:
            cells = [str(r["rank"]), md_escape(r["player"]), _assist_cell(r), fmt_adp(r),
                     fmt_area(r), fmt_time(r), str(r["layer"]), fmt_ge(r["area_mge"]),
                     str(r["depth"]), str(r["proof_lines"]), r["submitted_at"], _record_cell(r)]
            if budget is not None:
                cells.insert(9, "over" if r["over_budget"] else "ok")
            trs.append(cells)
        lines += [f"{h}# Ranked by area x time (lower is better; equal scores share a rank)", ""]
        lines += _md_table(header, aligns, trs) + ["", LAYER_NOTE, ""]
    if board["budget_ranking"] is not None:
        lines += [f"{h}# Best area x time under the depth budget (depth <= {budget})", ""]
        trs = [[("-" if r["rank"] is None else str(r["rank"])), md_escape(r["player"]),
                _assist_cell(r), fmt_adp(r), fmt_area(r), fmt_time(r), fmt_ge(r["area_mge"]),
                str(r["depth"]), "over budget" if r["rank"] is None else "ok", r["submitted_at"],
                _record_cell(r)] for r in board["budget_ranking"]]
        lines += _md_table(["rank", "player", "assisted by", ADP_HEAD, "area (um^2)", "time (ps)", "area (GE)",
                            "depth", "budget", "date", "record"],
                           ["r", "l", "l", "r", "r", "r", "r", "r", "l", "l", "l"], trs)
        lines.append("")
    if board["unranked"]:
        lines += [f"{h}# Not ranked", ""]
        trs = [[md_escape(r["player"]), fmt_area(r), fmt_time(r), fmt_ge(r["area_mge"]),
                str(r["depth"]), _record_cell(r), md_escape(r["reason"])] for r in board["unranked"]]
        lines += _md_table(["player", "area (um^2)", "time (ps)", "area (GE)", "depth", "record", "why"],
                           ["l", "r", "r", "r", "r", "l", "l"], trs) + [""]
    if _has_light(board):
        lines += [LIGHT_NOTE, ""]
    return "\n".join(lines)


def render_export(boards, pdk=DEFAULT_PDK):
    """All tasks' boards as one Markdown document (`pdk` "asap7": the boards of the ASAP7 view)."""
    parts = ["# svGolf leaderboard", "",
             "Generated by `leaderboard/leaderboard.py export` from the records under "
             "`leaderboard/data/`. Ranked by area x time (`leaderboard/combined.py`), lower is better: "
             "the sky130 A0' area in um^2 (`score/ppa.py`) times the time (the critical-path delay; on a "
             "clocked task, cycles x the clock period), in um^2 x ns. The Pareto layer of the two factors, "
             "area in GE and depth are extra columns; they rank nothing. A record without sky130 columns "
             "is not ranked until it is backfilled.", ""]
    if pdk == "asap7":
        parts = ["# svGolf leaderboard: the ASAP7 view", "",
                 "Generated by `leaderboard/leaderboard.py export --pdk asap7` from the records under "
                 "`leaderboard/data/` and their ASAP7 columns under `leaderboard/asap7/`. The same boards ranked by "
                 "area x time on the ASAP7 library instead of sky130 (a view a reader may choose; sky130 is the "
                 "default and the records' own columns).", ""]
    parts += [render_markdown(b, 2) for b in boards]
    return "\n".join(parts).rstrip("\n") + "\n"


def par_line(par):
    """The board's par line (`par`: `par_of`'s row, or None)."""
    if par is None:
        return (f"Par: none recorded (no record of `{REFERENCE_PLAYER}` ranks here; `leaderboard.py seed-references "
                "--task <task>` records the proved references).")
    return ("Par, the best proved reference by area x time (the ranked number; lower is better): "
            + fmt_par(par) + ".")


PARETO_EXPLORATION = "exploration: the board ranks area x time; # is the entry's rank there"
ADP_TEXT_HEAD = f"area x time {combined.UNIT_ASCII}"


def render_pareto_text(board):
    lines = []
    point = ", ".join(f"{k}={v}" for k, v in board["scoring_point"].items()) or "fixed size"
    lib = "ASAP7" if board.get("pdk") == "asap7" else "sky130"
    lines.append(f"{board['task']}: Pareto frontier of ({lib} area, time) at {point} "
                 f"({len(board['frontier'])} of {len(board['ranking'])} ranked records), {PARETO_EXPLORATION}")
    if "par" in board:
        lines.append("  " + par_line(board["par"]))
    if not board["frontier"]:
        lines.append("  (no ranked records)")
    else:
        heads = ("#", ADP_TEXT_HEAD, "area um^2", "time ps", "area GE", "depth")
        rows = [(str(r["rank"]), fmt_adp(r), fmt_area(r), fmt_time(r), fmt_ge(r["area_mge"]),
                 str(r["depth"]), r) for r in board["frontier"]]
        w = [max(len(head), *(len(x[k]) for x in rows)) for k, head in enumerate(heads)]
        lines.append("  " + " ".join(f"{head:>{n}}" for head, n in zip(heads, w))
                     + f"  {'player':<20} {'record':<12}  assisted by")
        for *cells, r in rows:
            lines.append("  " + " ".join(f"{c:>{n}}" for c, n in zip(cells, w))
                         + f"  {r['player']:<20} {r['record_hash'][:12]:<12}  "
                         + ("; ".join(r["assisted_by"]) or "none")
                         + ("  [light post-synthesis check]" if r.get("postsynth") == "light"
                            else ""))
    if board["unranked"]:
        lines.append(f"  not ranked ({len(board['unranked'])}):")
        for r in board["unranked"]:
            lines.append(f"    {r['record_hash'][:12]} {r['player']}: {r['reason']}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# the n-dimensional Pareto view over chosen axes (opt-in: `pareto --axes ...`)
# ---------------------------------------------------------------------------
#
# Exploration, like the default `pareto` (the board ranks area x time, `score_key`, and nothing here changes
# it): `pareto` without `--axes` prints the frontier of RANKED_AXES (sky130 A0' area, time). With `--axes`
# the frontier is taken over the named axes only, for the records that carry all of them
# (`--axes area_um2_sky130,time_ps` is the default `pareto` frontier). Every axis is "lower is better"
# and an exact integer (areas in um^2 are compared as integers in 1e-4 um^2, the unit the columns are
# exact in); a record is on the frontier iff no other record is at least as good on every axis and
# strictly better on one (ties are kept, as in the default `pareto`).

def _fmt_e4(v):
    """1e-4 um^2 as exact decimal text: 4604416 -> '460.4416'."""
    return f"{v // 10000}.{v % 10000:04d}"


# axis name -> (where, key, formatter of the exact integer)
AXES = {
    "area_mge": ("score", "area_mge", fmt_ge),
    "depth": ("score", "depth", str),
    "area_um2_sky130": ("ppa", "area_e4um2_sky130", _fmt_e4),
    # the ranked time: the delay of a combinational record, cycles x period of a clocked one (`ranked_columns`)
    "time_ps": ("ppa", "time_ps", str),
    "delay_ps_sky130": ("ppa", "delay_ps_sky130", str),
    "unit_depth": ("ppa", "unit_depth", str),
    "cells_sky130": ("ppa", "cells_sky130", str),
    # flow A1' (the `ppa.mapped` sub-object): a real abc -liberty mapping, an unranked research column set
    "area_um2_sky130_mapped_v1": ("mapped", "area_e4um2_sky130_mapped_v1", _fmt_e4),
    "mapped_delay_sky130_v1": ("mapped", "mapped_delay_sky130_v1", str),
    "mapped_cells_sky130_v1": ("mapped", "mapped_cells_sky130_v1", str),
    "mapped_levels_sky130_v1": ("mapped", "mapped_levels_sky130_v1", str),
}


def parse_axes(text):
    """`--axes a,b,c` -> ["a", "b", "c"]; Refused on an unknown or repeated axis or an empty list."""
    names = [x.strip() for x in str(text).split(",") if x.strip()]
    problems = []
    unknown = [n for n in names if n not in AXES]
    if unknown:
        problems.append(f"unknown axes {unknown} (known: {', '.join(AXES)})")
    if len(set(names)) != len(names):
        problems.append("an axis is named twice")
    if not names:
        problems.append("--axes needs at least one axis")
    if problems:
        raise Refused(problems)
    return names


def axis_values(rec, axes):
    """{axis: exact integer} of a record, or None if it lacks one of them (a record made before the
    PPA columns, or whose design the pinned flow could not weigh)."""
    out = {}
    for a in axes:
        where, key, _ = AXES[a]
        block = rec.get(where) if where == "score" else rec.get(PPA_KEY)
        if where in ("ppa", "mapped") and not (isinstance(block, dict) and block.get("available") is True):
            return None
        if where == "mapped":
            block = block.get(PPA_MAPPED_KEY)
            if not (isinstance(block, dict) and block.get("available") is True):
                return None
        v = ((ranked_columns(rec) or {}).get("time_ps") if a == "time_ps"
             else block.get(key) if isinstance(block, dict) else None)
        if not isinstance(v, int) or isinstance(v, bool):
            return None
        out[a] = v
    return out


def dominates_on(a, b, axes):
    """`a` beats `b` on `axes`: no worse on every one, strictly better on one."""
    return (all(a["values"][x] <= b["values"][x] for x in axes)
            and any(a["values"][x] < b["values"][x] for x in axes))


def axes_key(r, axes):
    return tuple(r["values"][x] for x in axes) + (r["submitted_at"], r["player"], r["record_hash"])


def pareto_on(rows, axes):
    """The non-dominated rows over `axes` (each row carries `values`), ties kept, in `axes_key` order."""
    rows = sorted(rows, key=lambda r: axes_key(r, axes))
    return [r for r in rows if not any(dominates_on(o, r, axes) for o in rows)]


def ppa_identity(pins_path=PPA_PINS):
    """What a record's PPA columns must have been computed under to be comparable with the current
    ones: the pins file's ppa_version, its sha256 and the pinned liberty's sha256 (read from the
    pins file; no liberty and no ppa.py needed). None if the pins file cannot be read."""
    try:
        with open(pins_path, "rb") as fh:
            raw = fh.read()
        pins = json.loads(raw.decode("utf-8"))
        return {"ppa_version": pins["ppa_version"], "ppa_pins_sha256": sha256_bytes(raw),
                "liberty_sha256": pins["liberty"]["sha256"]}
    except (OSError, ValueError, KeyError):
        return None


def ppa_setup_now(task, pins_path=PPA_PINS):
    """The timing setup a record's `ppa.setup` must name to be comparable with columns computed now for `task`
    (sky130_a0_v3): `input_drive`, the cell in front of every primary input (the task.json's `input_drive`, else the pins
    file's `timing.input_drive.default`: what score/ppa.py's `input_drive_of` gives, read here without ppa.py or the
    liberty), and the pins' `pi_slew_ps` and `po_load_ff`. A key the files cannot say is absent (it is then not compared);
    {} if nothing can be read."""
    out = {}
    try:
        with open(pins_path, "rb") as fh:
            timing = json.loads(fh.read().decode("utf-8"))["timing"]
        for k in ("pi_slew_ps", "po_load_ff"):
            if k in timing:
                out[k] = timing[k]
        out["input_drive"] = timing["input_drive"]["default"]
    except (OSError, ValueError, KeyError, TypeError):
        pass
    if isinstance(task, dict) and "input_drive" in task:
        out["input_drive"] = task["input_drive"]
    return out


def ppa_input_drive(block):
    """The cell a `ppa` block says drove its primary inputs (`setup.input_drive`, sky130_a0_v3), or None if it names
    none (a block of an earlier ppa_version, or not a block)."""
    s = block.get("setup") if isinstance(block, dict) else None
    d = s.get("input_drive") if isinstance(s, dict) else None
    return d if isinstance(d, str) else None


def ppa_drive_mismatch(block, input_drive):
    """Why the numeric `ppa` block is not comparable with columns weighed now under the task's `input_drive` (None if
    it is, or if `input_drive` is None: not compared). The drive is a task field, outside the pins file and so outside
    PPA_IDENTITY: a task that changes it makes its earlier records incomparable, not wrong. Pure."""
    got = ppa_input_drive(block)
    if input_drive is None or got == input_drive:
        return None
    return (f"PPA columns computed under another input drive ({got or 'none named'}; "
            f"the task's input drive is now {input_drive})")


def ppa_mapped_identity(pins_path=PPA_MAPPED_PINS, script_path=PPA_MAPPED_SCRIPT, a0_pins_path=PPA_PINS):
    """What a record's `ppa.mapped` columns must have been computed under to be comparable with the current ones (flow A1'):
    the mapped pins file's `ppa_mapped_version`, its sha256, the sha256 of the Yosys script, and the pinned liberty's sha256
    (from the mapped pins file). The Yosys/ABC build is compared through the flow (`flow_of`). None if a file cannot be read."""
    try:
        with open(pins_path, "rb") as fh:
            raw = fh.read()
        with open(script_path, "rb") as fh:
            script = fh.read()
        pins = json.loads(raw.decode("utf-8"))
        return {"ppa_mapped_version": pins["ppa_mapped_version"], "ppa_mapped_pins_sha256": sha256_bytes(raw),
                "ppa_mapped_script_sha256": sha256_bytes(script), "liberty_sha256": pins["liberty_sha256"]}
    except (OSError, ValueError, KeyError):
        return None


# ---------------------------------------------------------------------------
# the ASAP7 view (decided 2026-11-09)
# ---------------------------------------------------------------------------
#
# A reader may see the golf scores on ASAP7 instead of sky130 (the site's library selector; `board --pdk asap7`).
# The ASAP7 columns are flow A0' of `score/ppa.py --pdk asap7` (asap7_a0_v1: the same scored netlist, each gate its
# least-area ASAP7 build, repaired by buffering, timed under the ASAP7 setup; score/PPA.md, "ASAP7: an alternative
# library"). They live in leaderboard/asap7/<task>.json (ASAP7_SCHEMA), one entry per design FILE (its sha256) that the
# task's views show at the scoring point: every record (the players' and the reference player's), every proved
# reference and every baseline with a score there (`asap7_designs`). Each entry is BOUND to the sky130 side: its
# canonical text, canonical RTLIL, GE columns, cycles and scored netlist are the record's (for a reference or a
# baseline, tests/expected.json's GE columns and cycles), so an ASAP7 number is always about the netlist the record's
# sky130 numbers weigh (`asap7_binding_problems`). `asap7 --write` measures (Yosys and the five pinned ASAP7 liberty
# files), `asap7` checks the files offline, `asap7 --rescore` and plain `verify` re-derive them bit for bit.
# Deterministic: ppa.py's A0' is bit-exact run to run on either library (score/PPA.md), keys and lists are sorted, and
# nothing in the file is a clock reading.

ASAP7_SCHEMA = "svgolf-asap7/1"
ASAP7_RANKED_AXES = ("area_um2_asap7", "time_ps")
# what makes ASAP7 columns comparable with the ones weighed now: the pins' version and hash, the liberty SET's
# identity (score/ppa.py `set_sha256`) and the input drive (the asap7 pins' default: no task names one)
ASAP7_IDENTITY = ("ppa_version", "liberty_sha256", "ppa_pins_sha256", "input_drive")
ASAP7_TOP_KEYS = {"schema", "task", "scoring_point", "flow", "identity", "ppa_script_sha256", "designs"}
# an entry: the design file it is of and who shows it (`of`), its binding to the sky130 side, the ASAP7 columns
ASAP7_ENTRY_KEYS = ("sv_sha256", "of", "canonical_sha256", "rtlil_sha256", "netlist_sha256", "area_mge", "depth",
                    "area_e5um2", "delay_ps", "cycles", "time_ps", "cells", "flops", "buffers", "tie_cells",
                    "repaired_sha256", "table_reads_floored")
ASAP7_COMPARED = ASAP7_ENTRY_KEYS[2:]            # what a fresh weighing must reproduce exactly
ASAP7_OF_RE = re.compile(r"(record:[0-9a-f]{64}|reference:[A-Za-z0-9_.-]+|baseline:[A-Za-z0-9_.-]+)")
ASAP7_BOARD_NOTE = ("Library: ASAP7 (asap7sc7p5t rev 28, RVT, TT; predictive 7 nm, never fabricated; wire-free like "
                    "sky130's A0'), the view a reader may choose (decided 2026-11-09). The default and the records' own "
                    "columns are sky130; the ASAP7 columns are `score/ppa.py --pdk asap7` on the same scored netlist "
                    "(`leaderboard/asap7/<task>.json`), area in um^2 to 5 decimals.")


def asap7_identity(pins_path=PPA_PINS_ASAP7):
    """What ASAP7 columns must have been computed under to be comparable with the ones weighed now (ASAP7_IDENTITY):
    the pins' `ppa_version`, the pins file's sha256, the identity of the pinned liberty SET (score/ppa.py `set_sha256`:
    SHA-256 over `<file> <sha256>\\n` per file, in the pins' order) and the pins' default input drive. Read from the
    pins file alone (no liberty, no ppa.py). None if it cannot be read."""
    try:
        with open(pins_path, "rb") as fh:
            raw = fh.read()
        pins = json.loads(raw.decode("utf-8"))
        files = pins["liberty"]["files"]
        lib = sha256_bytes("".join(f"{f['file']} {f['sha256']}\n" for f in files).encode())
        return {"ppa_version": pins["ppa_version"], "ppa_pins_sha256": sha256_bytes(raw), "liberty_sha256": lib,
                "input_drive": pins["timing"]["input_drive"]["default"]}
    except (OSError, ValueError, KeyError, TypeError):
        return None


def asap7_path(task_name, asap7_dir=ASAP7_DIR):
    return os.path.join(asap7_dir, f"{task_name}.json")


def point_key(point):
    """A scoring point as tests/expected.json keys it: 'N=16', 'W=5,P=11', 'default' (task.json's order)."""
    return ",".join(f"{k}={v}" for k, v in point.items()) or "default"


def _nat(v):
    return isinstance(v, int) and not isinstance(v, bool) and v >= 0


def asap7_file_problems(data, task_name=None):
    """What is wrong with the contents of a leaderboard/asap7/<task>.json (a list of strings; [] for a good file).
    Pure. Checks the shape and the arithmetic (time = delay, or cycles x delay); whether the entries are the task's
    designs and bound to them is `asap7_check`'s."""
    if not isinstance(data, dict):
        return ["not a JSON object"]
    p = []
    keys = {k for k in data if not k.startswith("_")}
    if keys != ASAP7_TOP_KEYS:
        p.append(f"keys {sorted(keys ^ ASAP7_TOP_KEYS)} unexpected or missing")
    if data.get("schema") != ASAP7_SCHEMA:
        p.append(f"schema is {data.get('schema')!r}, not {ASAP7_SCHEMA!r}")
    if task_name is not None and data.get("task") != task_name:
        p.append(f"task is {data.get('task')!r}, not {task_name!r}")
    ident = data.get("identity")
    if not (isinstance(ident, dict) and set(ident) == set(ASAP7_IDENTITY)
            and all(isinstance(ident[k], str) for k in ASAP7_IDENTITY)):
        p.append(f"identity must name exactly {', '.join(ASAP7_IDENTITY)}")
    if not isinstance(data.get("scoring_point"), dict) or not isinstance(data.get("flow"), dict):
        p.append("scoring_point and flow must be objects")
    designs = data.get("designs")
    if not isinstance(designs, list):
        return p + ["designs is not a list"]
    seen = set()
    for k, e in enumerate(designs):
        where = f"designs[{k}]"
        if not isinstance(e, dict) or set(e) != set(ASAP7_ENTRY_KEYS):
            p.append(f"{where}: keys must be exactly {', '.join(ASAP7_ENTRY_KEYS)}")
            continue
        if not (isinstance(e["sv_sha256"], str) and SHA_RE.fullmatch(e["sv_sha256"])) or e["sv_sha256"] in seen:
            p.append(f"{where}: sv_sha256 is not a sha256, or not unique")
        seen.add(e["sv_sha256"])
        of = e["of"]
        if not (isinstance(of, list) and of and all(isinstance(x, str) and ASAP7_OF_RE.fullmatch(x) for x in of)
                and of == sorted(set(of))):
            p.append(f"{where}: `of` must be a sorted, non-empty list of record:<hash>, reference:<stem>, baseline:<stem>")
        for h in ("canonical_sha256", "rtlil_sha256", "netlist_sha256", "repaired_sha256"):
            if not (isinstance(e[h], str) and SHA_RE.fullmatch(e[h])):
                p.append(f"{where}: {h} is not a sha256")
        for n in ("area_mge", "depth", "area_e5um2", "delay_ps", "time_ps", "cells", "buffers", "tie_cells",
                  "table_reads_floored"):
            if not _nat(e[n]):
                p.append(f"{where}: {n} is not a non-negative integer")
        for n in ("cycles", "flops"):
            if e[n] is not None and not _nat(e[n]):
                p.append(f"{where}: {n} is neither null nor a non-negative integer")
        if _nat(e["delay_ps"]) and _nat(e["time_ps"]) and (e["cycles"] is None or _nat(e["cycles"])):
            want = e["delay_ps"] * (e["cycles"] if e["cycles"] is not None else 1)
            if e["time_ps"] != want:
                p.append(f"{where}: time_ps {e['time_ps']} is not " + ("cycles x delay_ps" if e["cycles"] is not None
                                                                      else "delay_ps") + f" ({want})")
    if [e.get("sv_sha256") for e in designs if isinstance(e, dict)] != sorted(
            e.get("sv_sha256") for e in designs if isinstance(e, dict) and isinstance(e.get("sv_sha256"), str)):
        p.append("designs are not in sv_sha256 order")
    return p


def read_asap7(task_name, asap7_dir=ASAP7_DIR):
    """(the task's ASAP7 table, None), (None, why) for a file that cannot be read or is malformed, or (None, None) when
    the task has none."""
    path = asap7_path(task_name, asap7_dir)
    if not os.path.isfile(path):
        return None, None
    try:
        with open(path, encoding="utf-8") as fh:
            data = json.load(fh)
    except (OSError, ValueError) as e:
        return None, f"{os.path.relpath(path, SVGOLF)}: not JSON: {e}"
    bad = asap7_file_problems(data, task_name)
    if bad:
        return None, f"{os.path.relpath(path, SVGOLF)}: " + "; ".join(bad[:5])
    return data, None


def load_asap7(task_name, asap7_dir=ASAP7_DIR, warn=None):
    """The task's ASAP7 table (`read_asap7`), or None (`warn` is told why, for a file that is there but bad)."""
    data, why = read_asap7(task_name, asap7_dir)
    if why and warn:
        warn(f"{why}: its ASAP7 columns are not used")
    return data


def asap7_entry(table, sv_sha256):
    """The entry of `table` for the design file with this sha256, or None."""
    if not isinstance(table, dict):
        return None
    return next((e for e in table.get("designs") or [] if e.get("sv_sha256") == sv_sha256), None)


def asap7_binding_problems(entry, rec):
    """Where an ASAP7 entry is not about the record's own netlist: its canonical text, canonical RTLIL, GE columns,
    cycles (a clocked record's) and scored netlist (the record's `ppa.netlist_sha256`, when it has sky130 columns: the
    scored netlist does not depend on the library) against the record's. [] when it is bound. Pure."""
    sc = rec.get("score") or {}
    p = []
    if entry.get("canonical_sha256") != rec.get("canonical_sha256"):
        p.append("canonical text sha256 differs")
    if sc.get("rtlil_sha256") and entry.get("rtlil_sha256") != sc["rtlil_sha256"]:
        p.append("canonical RTLIL sha256 differs")
    for k in ("area_mge", "depth"):
        if entry.get(k) != sc.get(k):
            p.append(f"{k} {entry.get(k)!r}, the record's {sc.get(k)!r}")
    if entry.get("cycles") != sc.get("cycles"):
        p.append(f"cycles {entry.get('cycles')!r}, the record's {sc.get('cycles')!r}")
    b = rec.get(PPA_KEY)
    if isinstance(b, dict) and b.get("available") is True and b.get("netlist_sha256") \
            and entry.get("netlist_sha256") != b["netlist_sha256"]:
        p.append("scored netlist sha256 differs from the record's ppa.netlist_sha256")
    return p


def asap7_columns(rec, table):
    """{area_e5um2, time_ps, cycles, period_ps} of a record in the ASAP7 view (`cycles`, `period_ps` None for a
    combinational record, as `ranked_columns`), from its entry in `table`; None without an entry bound to it."""
    e = asap7_entry(table, ((rec.get("files") or {}).get("sv") or {}).get("sha256"))
    if e is None or asap7_binding_problems(e, rec):
        return None
    clocked = e["cycles"] is not None
    return {"area_e5um2": e["area_e5um2"], "time_ps": e["time_ps"], "cycles": e["cycles"] if clocked else None,
            "period_ps": e["delay_ps"] if clocked else None}


def asap7_table_mismatch(table, task, *, identity=None, flow=None):
    """Why a task's ASAP7 table as a whole is not comparable with columns weighed now (another scoring point, another
    ASAP7 version or input drive than `identity`, measured under another flow than `flow`, the current flow of the
    task's kind), or None. Pure."""
    if table.get("scoring_point") != scoring_point(task):
        return f"ASAP7 columns measured at {table.get('scoring_point')}, the task's scoring point is {scoring_point(task)}"
    ident = table.get("identity") or {}
    if identity is not None:
        other = [k for k in ASAP7_IDENTITY if ident.get(k) != identity.get(k)]
        if other:
            return "ASAP7 columns computed under another version (" + ", ".join(other) + " differ)"
    if flow is not None:
        diff = flow_mismatch(table.get("flow") or {}, flow)
        if diff:
            return "ASAP7 columns measured under another flow (" + ", ".join(diff) + " differ)"
    return None


def asap7_mismatch(rec, task, table, *, identity=None, flow=None):
    """Why `rec` has no comparable ASAP7 columns (the ASAP7 view's half of `unranked_reason`), or None. Pure."""
    if table is None:
        return (f"no ASAP7 columns for task {task['name']} yet (leaderboard/asap7/{task['name']}.json; "
                "`leaderboard.py asap7 --write` measures them)")
    why = asap7_table_mismatch(table, task, identity=identity, flow=flow)
    if why:
        return why
    e = asap7_entry(table, rec["files"]["sv"]["sha256"])
    if e is None:
        return "no ASAP7 columns for its design yet (`leaderboard.py asap7 --write` measures them)"
    bad = asap7_binding_problems(e, rec)
    if bad:
        return "its ASAP7 columns are not of its netlist (" + "; ".join(bad) + ")"
    return None


def asap7_designs(task, records, expected, *, tasks_dir=DEFAULT_TASKS, data_dir=DEFAULT_DATA, svgolf=SVGOLF):
    """The design files the ASAP7 view of `task` shows at its scoring point, by sha256: {sv_sha256: {"src" (a path),
    "of" (sorted: record:<hash>, reference:<stem>, baseline:<stem>), "want" (what the entry must be bound to: the GE
    columns and cycles from every source, and a record's canonical text, RTLIL and scored netlist), "conflicts" (two
    sources that disagree on one of them)}}. The records are `records` of the task at its scoring point (every player,
    the reference player's too); the references are task.json's, the baselines tests/expected.json's, each with a
    score at the scoring point (`expected`: tests/expected.json). Reads the design files (their sha256), nothing else."""
    name = task["name"]
    point = scoring_point(task)
    key = point_key(point)
    exp = (expected.get("tasks") or {}).get(name, {})
    out = {}

    def add(sha, src, tag, want):
        d = out.setdefault(sha, {"src": src, "of": set(), "want": {}, "conflicts": []})
        d["of"].add(tag)
        for k, v in want.items():
            if v is None:
                continue
            if k in d["want"] and d["want"][k] != v:
                d["conflicts"].append(f"{k}: {tag} says {v!r}, another source {d['want'][k]!r}")
            d["want"].setdefault(k, v)

    def from_scores(e):
        s = (e.get("scores") or {}).get(key) or {}
        if "area_mge" not in s:
            return None
        return {"area_mge": s["area_mge"], "depth": s["depth"], "cycles": s.get("cycles")}

    for ref in task.get("references") or []:
        stem = os.path.splitext(os.path.basename(ref["sv"]))[0]
        want = from_scores((exp.get("references") or {}).get(stem, {}))
        if want is None:
            continue
        src = os.path.join(tasks_dir, name, ref["sv"])
        add(sha256_file(src), src, f"reference:{stem}", want)
    for stem, e in sorted((exp.get("baselines") or {}).items()):
        want = from_scores(e)
        if want is None:
            continue
        src = os.path.join(svgolf, "tests", name, e.get("sv", f"baselines/{stem}.sv"))
        add(sha256_file(src), src, f"baseline:{stem}", want)
    for rec in sorted(records, key=lambda r: r["record_hash"]):
        if rec.get("task") != name or rec["score"]["scoring_point"] != point:
            continue
        sc = rec["score"]
        b = rec.get(PPA_KEY)
        net = b.get("netlist_sha256") if isinstance(b, dict) and b.get("available") is True else None
        src = record_paths(data_dir, name, rec["record_hash"])[1]
        add(rec["files"]["sv"]["sha256"], src, f"record:{rec['record_hash']}",
            {"area_mge": sc["area_mge"], "depth": sc["depth"], "cycles": sc.get("cycles"),
             "canonical_sha256": rec["canonical_sha256"], "rtlil_sha256": sc.get("rtlil_sha256"),
             "netlist_sha256": net})
    for d in out.values():
        d["of"] = sorted(d["of"])
    return out


def asap7_want_problems(entry, want):
    """Where an entry differs from what its design's sources say (`asap7_designs`' `want`). Pure."""
    out = [f"{k}: the entry has {entry.get(k)!r}, the design's sources {v!r}" for k, v in sorted(want.items())
           if k != "cycles" and entry.get(k) != v]
    if entry.get("cycles") != want.get("cycles"):
        out.append(f"cycles: the entry has {entry.get('cycles')!r}, the design's sources {want.get('cycles')!r}")
    return out


def run_asap7(sv, task_dir, *, ppa_py=PPA_PY, seq=False, timeout=3600):
    """score/ppa.py --pdk asap7 --no-mapped (and --seq for the clocked flow) on one design at the task's scoring point:
    (score.py's result, the ASAP7 `ppa` block). RuntimeError with the reason if it cannot weigh (no ASAP7 liberty here,
    a flow failure, an illegal netlist)."""
    cmd = [checker_python(), ppa_py, sv, "--task", task_dir, "--pdk", "asap7", "--no-mapped"] + (["--seq"] if seq else [])
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    try:
        out = json.loads(proc.stdout)
    except ValueError:
        out = {}
    if proc.returncode == 0 and isinstance(out.get("score"), dict) and isinstance(out.get("ppa"), dict):
        return out["score"], out["ppa"]
    why = " ".join(str(out.get("error") or proc.stderr[-400:] or f"exit {proc.returncode}").split())
    raise RuntimeError(f"ppa.py --pdk asap7: {why[:400]}")


def asap7_columns_of(score, ppa, cycles):
    """An entry's measured part (ASAP7_COMPARED) from ppa.py's result; `cycles` is the design's latency at the scoring
    point (a clocked design; None for a combinational one), which the time multiplies."""
    if ppa.get("pdk") != "asap7":
        raise RuntimeError(f"ppa.py weighed on {ppa.get('pdk')!r}, not asap7")
    rp = ppa.get("repair") or {}
    delay = ppa["delay_ps_asap7"]
    return {"canonical_sha256": ((score.get("sources") or [{}])[0]).get("canonical_sha256"),
            "rtlil_sha256": score.get("rtlil_sha256"), "netlist_sha256": ppa["netlist_sha256"],
            "area_mge": score["area_mge"], "depth": score["depth"],
            "area_e5um2": ppa["area_e5um2_asap7"], "delay_ps": delay, "cycles": cycles,
            "time_ps": delay * (cycles if cycles is not None else 1), "cells": ppa["cells_asap7"],
            "flops": ppa.get("flops"), "buffers": rp.get("buffers"), "tie_cells": rp.get("tie_cells"),
            "repaired_sha256": rp.get("netlist_sha256"),
            "table_reads_floored": (ppa.get("legality") or {}).get("table_reads_floored")}


def asap7_check(task, table, designs, *, identity=None, flow=None, rescore=None):
    """Check a task's ASAP7 table against the designs it must cover (`asap7_designs`): (fails, notes). FAIL: a design
    of the task without an entry, an entry for no design or with another `of`, an entry not bound to its design's
    sources (GE columns, cycles, a record's canonical text, RTLIL and scored netlist), two sources of one design that
    disagree; with `rescore(entry)` (it returns the fresh ASAP7_COMPARED columns, or raises), a column that a fresh
    weighing does not reproduce. Notes (not failures): a table of another ASAP7 version, scoring point or flow than now
    (it is then not compared with a rescore)."""
    fails, notes = [], []
    entries = {e["sv_sha256"]: e for e in table["designs"]}
    for sha in sorted(set(designs) - set(entries)):
        fails.append(f"no entry for {', '.join(designs[sha]['of'])} ({sha[:12]})")
    for sha in sorted(set(entries) - set(designs)):
        fails.append(f"an entry for no design of the task now: {', '.join(entries[sha]['of'])} ({sha[:12]})")
    stale = asap7_table_mismatch(table, task, identity=identity, flow=flow)
    if stale:
        notes.append(stale + ": not comparable (measure again with `asap7 --write`)")
    for sha in sorted(set(designs) & set(entries)):
        d, e = designs[sha], entries[sha]
        who = ", ".join(d["of"])
        fails += [f"{who}: {c}" for c in d["conflicts"]]
        if e["of"] != d["of"]:
            fails.append(f"{sha[:12]}: `of` is {e['of']}, the design is now {d['of']}")
        if not stale:
            fails += [f"{who}: {p}" for p in asap7_want_problems(e, d["want"])]
        if rescore is not None and not stale:
            try:
                got = rescore(e, d)
            except Exception as ex:   # infrastructure (no ASAP7 liberty) or a flow failure
                notes.append(f"{who}: not re-weighed ({ex})")
                continue
            diffs = [f"{who}: {k} recorded {e.get(k)!r}, now {got.get(k)!r}" for k in ASAP7_COMPARED
                     if e.get(k) != got.get(k)]
            fails += diffs
    return fails, notes


def build_axes_view(task, records, axes, *, flow=None, identity=None, mapped_identity=None, unassisted=False,
                    input_drive=None, statement=None):
    """The Pareto view of one task over `axes` (names of AXES). `records` are its records. Records
    scored at another point, or under another flow (when `flow` is given), or whose PPA columns
    were computed under another `ppa_version`/liberty/pins than `identity` (when given, and an axis
    is a PPA axis), or under another input drive than the task's `input_drive` (when given, and an
    axis is an A0' axis: `ppa_setup_now(task)["input_drive"]`; a block that names none is another
    drive) are `not_shown` with the reason, like the default board's "Not ranked"; so are records
    that lack an axis. Pure."""
    point = scoring_point(task)
    uses_ppa = any(AXES[a][0] == "ppa" for a in axes)
    uses_mapped = any(AXES[a][0] == "mapped" for a in axes)
    shown, hidden = [], []
    for rec in sorted((r for r in records if r["task"] == task["name"]),
                      key=lambda r: row_key(row_of(r))):
        if unassisted and rec["assisted_by"]:
            continue
        row = row_of(rec)
        vals = axis_values(rec, axes)
        why = None
        if rec["score"]["scoring_point"] != point:
            why = f"scored at {rec['score']['scoring_point']}, not at {point}"
        elif statement is not None and statement_mismatch(rec, statement):
            why = statement_mismatch(rec, statement)
        elif kind_flow_mismatch(rec, task):
            why = kind_flow_mismatch(rec, task)
        elif flow is not None and flow_mismatch(flow_of(rec), flow):
            why = "checked under another flow (" + ", ".join(flow_mismatch(flow_of(rec), flow)) + " differ)"
        elif vals is None:
            b = rec.get(PPA_KEY)
            mb = b.get(PPA_MAPPED_KEY) if isinstance(b, dict) else None
            why = ("no PPA columns (a record made before them)" if b is None
                   else "the PPA columns were not computed: " + str((b or {}).get("reason", "?"))[:120]
                   if isinstance(b, dict) and b.get("available") is False
                   else "the mapped (A1') columns were not computed: " + str(mb.get("reason", "?"))[:120]
                   if uses_mapped and isinstance(mb, dict) and mb.get("available") is False
                   else "no mapped (A1') columns (a record made before them)" if uses_mapped and mb is None
                   else "lacks an axis")
        elif uses_ppa and identity is not None and any(rec[PPA_KEY].get(k) != identity.get(k)
                                                       for k in PPA_IDENTITY):
            why = ("PPA columns computed under another version ("
                   + ", ".join(k for k in PPA_IDENTITY if rec[PPA_KEY].get(k) != identity.get(k)) + " differ)")
        elif uses_ppa and ppa_drive_mismatch(rec[PPA_KEY], input_drive):
            why = ppa_drive_mismatch(rec[PPA_KEY], input_drive)
        elif uses_mapped and mapped_identity is not None and any(
                rec[PPA_KEY][PPA_MAPPED_KEY].get(k) != mapped_identity.get(k) for k in PPA_MAPPED_IDENTITY):
            why = ("mapped (A1') columns computed under another version ("
                   + ", ".join(k for k in PPA_MAPPED_IDENTITY
                               if rec[PPA_KEY][PPA_MAPPED_KEY].get(k) != mapped_identity.get(k)) + " differ)")
        if why:
            hidden.append(dict(row, reason=why))
        else:
            shown.append(dict(row, values=vals))
    front = pareto_on(shown, axes)
    gone = {id(r) for r in front}
    rest = [r for r in sorted(shown, key=lambda r: axes_key(r, axes)) if id(r) not in gone]

    def keyed(r):
        # each value is named after the RECORD FIELD it was read from, so the unit is in the name:
        # axis `area_um2_sky130` is `values.area_e4um2_sky130` (an integer in 1e-4 um^2), the record's own key
        return dict(r, values={AXES[a][1]: r["values"][a] for a in axes})
    return {"task": task["name"], "axes": list(axes), "axis_fields": {a: AXES[a][1] for a in axes},
            "scoring_point": point,
            "ppa_identity": identity if uses_ppa else None,
            "input_drive": input_drive if uses_ppa else None,
            "ppa_mapped_identity": mapped_identity if uses_mapped else None, "flow_checked": flow is not None,
            "frontier": [keyed(r) for r in front], "dominated": [keyed(r) for r in rest],
            "not_shown": hidden, "unassisted_only": bool(unassisted)}


def render_axes_text(view):
    axes = view["axes"]
    point = ", ".join(f"{k}={v}" for k, v in view["scoring_point"].items()) or "fixed size"
    n = len(view["frontier"]) + len(view["dominated"])
    lines = [f"{view['task']}: Pareto frontier over ({', '.join(axes)}) at {point} "
             f"({len(view['frontier'])} of {n} records that carry the axes), exploration: the board ranks "
             "area x time"]
    if not view["frontier"]:
        lines.append("  (no record carries all the axes)")
    else:
        fld = view["axis_fields"]
        cols = [max(len(a), *(len(AXES[a][2](r["values"][fld[a]])) for r in view["frontier"])) for a in axes]
        lines.append("  " + " ".join(f"{a:>{w}}" for a, w in zip(axes, cols))
                     + f"  {'player':<20} {'record':<12}  assisted by")
        for r in view["frontier"]:
            lines.append("  " + " ".join(f"{AXES[a][2](r['values'][fld[a]]):>{w}}" for a, w in zip(axes, cols))
                         + f"  {r['player']:<20} {r['record_hash'][:12]:<12}  "
                         + ("; ".join(r["assisted_by"]) or "none")
                         + ("  [light post-synthesis check]" if r.get("postsynth") == "light" else ""))
    if view["not_shown"]:
        lines.append(f"  not shown ({len(view['not_shown'])}):")
        for r in view["not_shown"]:
            lines.append(f"    {r['record_hash'][:12]} {r['player']}: {r['reason']}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# storage
# ---------------------------------------------------------------------------

def record_paths(data_dir, task, record_hash):
    base = os.path.join(data_dir, task, record_hash)
    return base + ".json", base + ".sv", base + ".lean"


def store_record(data_dir, rec, sv_bytes, lean_bytes):
    """Write the record and the two submitted files; returns the record's path.
    Refuses to overwrite."""
    jpath, spath, lpath = record_paths(data_dir, rec["task"], rec["record_hash"])
    if any(os.path.exists(x) for x in (jpath, spath, lpath)):
        raise Refused([f"{os.path.relpath(jpath)} already exists"])
    os.makedirs(os.path.dirname(jpath), exist_ok=True)
    for path, data in ((spath, sv_bytes), (lpath, lean_bytes)):
        with open(path, "wb") as fh:
            fh.write(data)
    with open(jpath, "w", encoding="utf-8") as fh:
        fh.write(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    return jpath


def load_records(data_dir, task=None):
    """[(path, record-or-None, error-or-None)] in file-name order. A file that
    is not valid JSON comes back with its error (verify reports it)."""
    out = []
    tasks = [task] if task else (sorted(os.listdir(data_dir)) if os.path.isdir(data_dir) else [])
    for t in tasks:
        d = os.path.join(data_dir, t)
        if not os.path.isdir(d):
            continue
        for name in sorted(os.listdir(d)):
            if not name.endswith(".json"):
                continue
            path = os.path.join(d, name)
            try:
                with open(path, encoding="utf-8") as fh:
                    out.append((path, json.load(fh), None))
            except (OSError, ValueError) as e:
                out.append((path, None, str(e)))
    return out


def intact(path, rec):
    """The cheap tamper tripwire the boards apply before trusting a record: it
    is well-formed, its record_hash is the hash of its content and the name
    of its file. (A forger who recomputes the hash and renames the file gets
    past this; `verify` and a re-check are the defence against that.)"""
    return (rec is not None and not validate_record(rec)
            and compute_record_hash(rec) == rec["record_hash"]
            and os.path.basename(path) == rec["record_hash"] + ".json")


def good_records(loaded, warn=None):
    """The intact records among `load_records`' results; `warn(msg)` is told
    about the rest."""
    out = []
    for path, rec, _ in loaded:
        if intact(path, rec):
            out.append(rec)
        elif warn:
            warn(f"skipping {os.path.basename(os.path.dirname(path))}/{os.path.basename(path)}: "
                 "not an intact record (run `leaderboard.py verify`)")
    return out


# ---------------------------------------------------------------------------
# verification
# ---------------------------------------------------------------------------

class VerifyResult:
    def __init__(self, label):
        self.label, self.fails, self.stale, self.notes = label, [], [], []

    @property
    def status(self):
        return "FAIL" if self.fails else ("stale" if self.stale else "ok")


def verify_record(path, rec, task=None, *, flow=None, current_files=None, rescore=None,
                  recheck=None, ppa_identity=None, ppa_setup=None, statement=None, asap7_view=None):
    """Verify one stored record at `path` (a `.json` next to its two files).

    Always: the record is well-formed, its `record_hash` is the hash of its
    canonical JSON and the file's name, the two stored files exist and have the
    recorded sha256, the score arithmetic is consistent (area = sum of the gate
    weights of the GE table of the record's flow, `score/ge.json` or, for a clocked
    record, `score/ge_seq.json`, when that table is the recorded one), the axioms
    are within the task's allowed set.

    `rescore(sv_path)` (optional): returns score.py's result for the stored
    design; the score, gate mix, canonical text hash and canonical RTLIL hash
    must equal the record's (skipped, with a note, if the flow has changed).
    `recheck(sv_path, lean_path)` (optional): returns check.py's full result;
    it must accept, with the same canonical hash, axioms and (same flow) score.

    A record checked under another flow than the current `flow` (the current flow
    of the task's kind, `current_flow(svgolf, task_flow(task))`), or of another
    flow than its task's kind is scored under (`kind_flow_mismatch`), is `stale`
    (not a failure): its score can no longer be reproduced or compared.

    `ppa_identity` (`ppa_identity()`) and `ppa_setup` (`ppa_setup_now(task)`, optional): a record
    whose sky130 columns are of the current identity must name the timing setup the task's
    configuration gives now. Its `setup.input_drive` another than the task's (`task.json`
    `input_drive`, a task field outside the pins file): `stale`, the columns are not compared
    (rescore, recheck) and the views do not rank them. Its `pi_slew_ps` / `po_load_ff` other than
    the pins file it names: FAIL (that file cannot have given them). A rescore or recheck compares
    the whole `setup` with the fresh weighing's (PPA_COMPARED).

    `asap7_view` (optional, the ASAP7 view, decided 2026-11-09): {"table": the task's leaderboard/asap7/<task>.json or
    None, "error": why that file is unreadable or malformed (FAIL), "identity": `asap7_identity()`, "rescore":
    sv_path -> the fresh ASAP7_COMPARED columns, or None}. The record's entry must be bound to it (canonical text,
    RTLIL, GE columns, cycles, scored netlist: FAIL otherwise, `asap7_binding_problems`); no entry, or a table of
    another ASAP7 version or flow, is a note (the view lacks the record; the record is no less valid); with
    `rescore` a fresh weighing must reproduce the entry exactly (FAIL)."""
    res = VerifyResult(os.path.basename(path))
    bad = validate_record(rec)
    if bad:
        res.fails += [f"malformed record: {b}" for b in bad]
        return res
    stem = os.path.basename(path)[:-5]
    if compute_record_hash(rec) != rec["record_hash"]:
        res.fails.append("record_hash does not match the record's content (edited?)")
    if stem != rec["record_hash"]:
        res.fails.append(f"file name {stem} is not the record_hash")
    if os.path.basename(os.path.dirname(path)) != rec["task"]:
        res.fails.append(f"stored under {os.path.basename(os.path.dirname(path))!r}, "
                         f"record says task {rec['task']!r}")
    d = os.path.dirname(path)
    stored = {}
    for kind, ext in (("sv", ".sv"), ("lean", ".lean")):
        fpath = os.path.join(d, stem + ext)
        stored[kind] = fpath
        if not os.path.isfile(fpath):
            res.fails.append(f"stored {kind} file {stem + ext} is missing")
        elif sha256_file(fpath) != rec["files"][kind]["sha256"]:
            res.fails.append(f"stored {kind} file {stem + ext} does not have the recorded sha256")
    if record_mode(rec["postsynth"]) == "light":
        res.notes.append("postsynth: this record's check ran in LIGHT mode (a local record; "
                         "`verify --full` rechecks it in full mode)")
    sc, ck = rec["score"], rec["checker"]
    ge_name = FLOW_FILES[record_flow(rec)][1]       # the GE table of the record's own flow
    ge_path = os.path.join(SVGOLF, "score", ge_name)
    if os.path.isfile(ge_path) and sha256_file(ge_path) == ck["ge_table_sha256"]:
        with open(ge_path, encoding="utf-8") as fh:
            ge = {k: round(v * 1000) for k, v in json.load(fh).items() if not k.startswith("_")}
        unknown = sorted(set(sc["gates"]) - set(ge))
        if unknown:
            res.fails.append(f"gate types the GE table does not price: {unknown}")
        elif sum(ge[g] * n for g, n in sc["gates"].items()) != sc["area_mge"]:
            res.fails.append(f"score.area_mge is not the sum of the gate weights in score/{ge_name}")
    else:
        res.notes.append("GE table differs from the recorded one: area arithmetic not rechecked")
    if task is not None:
        allowed = set(task.get("allowed_axioms", ["propext", "Classical.choice", "Quot.sound"]))
        extra = sorted(set(rec["proof"]["axioms"]) - allowed)
        if extra:
            res.fails.append(f"axioms outside the task's allowed set: {extra}")
        if sc["scoring_point"] != scoring_point(task):
            res.stale.append(f"scored at {sc['scoring_point']}, the task's scoring point is now "
                             f"{scoring_point(task)}")
    same_flow = True
    if task is not None and kind_flow_mismatch(rec, task):
        same_flow = False
        res.stale.append(kind_flow_mismatch(rec, task) + ": the score is not comparable with the task's")
    if flow is not None:
        diff = flow_mismatch(flow_of(rec), flow)
        if diff:
            same_flow = False
            res.stale.append("checked under another flow (" + ", ".join(diff)
                             + " differ): the score is no longer reproducible or comparable")
    if statement is not None and statement_mismatch(rec, statement):
        res.stale.append(statement_mismatch(rec, statement) + ": not ranked")
    if current_files is not None:
        changed = sorted(k for k, v in ck["files"].items() if current_files.get(k) != v)
        if changed:
            res.notes.append("checker files changed since this record: " + ", ".join(changed))
    # the sky130 columns' timing setup against what the task's configuration gives now (sky130_a0_v3); a block of
    # another identity is not comparable anyway (the rescore says so) and is not looked at here
    drive_stale = False
    pb = rec.get(PPA_KEY)
    if (ppa_identity is not None and ppa_setup and isinstance(pb, dict) and pb.get("available") is True
            and all(pb.get(k) == ppa_identity.get(k) for k in PPA_IDENTITY)):
        setup = pb.get("setup") if isinstance(pb.get("setup"), dict) else {}
        for k in ("pi_slew_ps", "po_load_ff"):
            if k in ppa_setup and setup.get(k) != ppa_setup[k]:
                res.fails.append(f"ppa.setup.{k} is {setup.get(k)!r}, but the pins file the block names "
                                 f"(ppa_pins_sha256) gives {ppa_setup[k]!r}")
        why = ppa_drive_mismatch(pb, ppa_setup.get("input_drive"))
        if why:
            drive_stale = True
            res.stale.append(why + ": not comparable with columns weighed now, and not ranked with them")
    if res.fails:
        return res
    if rescore is not None:
        if not same_flow:
            res.notes.append("rescore skipped: the flow has changed")
        else:
            try:
                got = rescore(stored["sv"])
            except Exception as e:  # infrastructure or a scoring refusal
                res.fails.append(f"rescore failed: {e}")
                got = None
            if got is not None:
                want = {"area_mge": sc["area_mge"], "depth": sc["depth"], "gates": sc["gates"],
                        "num_gates": sc["num_gates"]}
                diffs = [f"{k}: recorded {want[k]!r}, rescored {got.get(k)!r}"
                         for k in want if got.get(k) != want[k]]
                gcanon = ((got.get("sources") or [{}])[0]).get("canonical_sha256")
                if gcanon != rec["canonical_sha256"]:
                    diffs.append("canonical text sha256 differs")
                if sc.get("rtlil_sha256") and got.get("rtlil_sha256") != sc["rtlil_sha256"]:
                    diffs.append("canonical RTLIL sha256 differs")
                res.fails += [f"rescore: {d}" for d in diffs]
                if not diffs:
                    res.notes.append("rescored: same score")
                _compare_ppa(res, rec, got.get("ppa"), "rescore", strict=False, drive_stale=drive_stale)
    if recheck is not None:
        try:
            got = recheck(stored["sv"], stored["lean"])
        except Exception as e:
            res.fails.append(f"recheck failed: {e}")
            got = None
        if got is not None:
            if got.get("accepted") is not True:
                res.fails.append(f"recheck: check.py no longer accepts it (stage "
                                 f"{got.get('stage')!r}: {str((got.get('errors') or ['?'])[0])[:200]})")
            else:
                if _get(got, "stages", "source", "canonical_sha256") != rec["canonical_sha256"]:
                    res.fails.append("recheck: canonical text sha256 differs")
                axioms = sorted(_get(got, "stages", "comparator", "result", "axioms", default=[]))
                if axioms != rec["proof"]["axioms"]:
                    res.fails.append(f"recheck: axioms {axioms} differ from the recorded "
                                     f"{rec['proof']['axioms']}")
                # a clocked record's latency at each point (F8, 2026-11-08: the kernel's `lat p`, which validation
                # cannot re-derive) against the fresh check's: a proof fact, so compared whatever the flow
                if record_flow(rec) == SEQ_FLOW:
                    now = {x.get("point"): x.get("latency")
                           for x in (_get(got, "stages", "postsynth", "points", default=None) or [])
                           if isinstance(x, dict)}
                    for q in rec["postsynth"]["points"]:
                        if q["point"] not in now:
                            res.fails.append(f"recheck: no post-synthesis check at {q['point']}")
                        elif now[q["point"]] != q["latency"]:
                            res.fails.append(f"recheck: the latency at {q['point']} recorded {q['latency']!r}, now "
                                             f"{now[q['point']]!r}")
                if same_flow:
                    gs = got.get("score") or {}
                    for k in ("area_mge", "depth", "gates"):
                        if gs.get(k) != sc[k]:
                            res.fails.append(f"recheck: {k} recorded {sc[k]!r}, now {gs.get(k)!r}")
                else:
                    res.notes.append("recheck: accepted; score not compared (the flow has changed)")
                if same_flow:
                    _compare_ppa(res, rec, got.get("ppa"), "recheck", strict=True, drive_stale=drive_stale)
                elif isinstance(rec.get(PPA_KEY), dict) and rec[PPA_KEY].get("available") is True:
                    # the netlist, its area and its hash legitimately differ under another Yosys/flow: STALE
                    # (above), never FAIL; the identity hashes of PPA_IDENTITY do not cover the flow
                    res.notes.append("recheck: ppa columns not compared (the flow has changed)")
                if not any(f.startswith("recheck") for f in res.fails):
                    res.notes.append("rechecked: accepted, same canonical text and axioms")
    if asap7_view is not None and task is not None:
        _verify_asap7(res, rec, task, asap7_view, stored["sv"])
    return res


def _verify_asap7(res, rec, task, view, sv_path):
    """`verify_record`'s ASAP7 part (its docstring)."""
    if view.get("error"):
        res.fails.append(f"asap7: {view['error']}")
        return
    table = view.get("table")
    if table is None:
        res.notes.append(f"ASAP7 view: no columns for task {task['name']} yet")
        return
    e = asap7_entry(table, rec["files"]["sv"]["sha256"])
    if e is None:
        res.notes.append("ASAP7 view: no columns for this design yet (`asap7 --write`)")
        return
    other_flow = flow_mismatch(table.get("flow") or {}, flow_of(rec))
    if other_flow:
        res.notes.append("ASAP7 columns measured under another flow than this record's (" + ", ".join(other_flow)
                         + " differ): not compared")
        return
    bad = asap7_binding_problems(e, rec)
    res.fails += [f"asap7: the entry for this design is not of its netlist: {b}" for b in bad]
    if bad:
        return
    stale = asap7_table_mismatch(table, task, identity=view.get("identity"))
    if stale:
        res.notes.append(stale + ": not re-weighed")
        return
    if view.get("rescore") is None:
        res.notes.append("ASAP7 columns bound to the record")
        return
    try:
        got = view["rescore"](sv_path)
    except Exception as ex:     # infrastructure (no ASAP7 liberty here) or a flow failure
        res.notes.append(f"ASAP7 columns not re-weighed ({ex})")
        return
    diffs = [f"asap7: {k} recorded {e.get(k)!r}, now {got.get(k)!r}" for k in ASAP7_COMPARED if e.get(k) != got.get(k)]
    res.fails += diffs
    if not diffs:
        res.notes.append("ASAP7 columns reproduced")


# the columns a fresh weighing must reproduce exactly (the provenance hashes, and the input drive, decide whether it may be
# compared); `setup` is the timing setup the block says it was weighed under (sky130_a0_v3: its `input_drive` included)
PPA_COMPARED = ("area_e4um2_sky130", "delay_ps_sky130", "unit_depth", "cells_sky130",
                "cell_hist_sky130", "constants", "netlist_sha256", "setup")
PPA_IDENTITY = ("ppa_version", "liberty_sha256", "ppa_pins_sha256")
# flow A1': the mapped columns a fresh mapping must reproduce exactly, and what decides whether it may be compared (the Yosys/
# ABC build is part of it too: it is compared here, as the tool builds are recorded in the block)
PPA_MAPPED_COMPARED = ("area_e4um2_sky130_mapped_v1", "mapped_delay_sky130_v1", "mapped_cells_sky130_v1",
                       "mapped_cell_hist_sky130_v1", "mapped_levels_sky130_v1", "constants", "rtlil_sha256", "netlist_sha256")
PPA_MAPPED_IDENTITY = ("ppa_mapped_version", "liberty_sha256", "ppa_mapped_pins_sha256", "ppa_mapped_script_sha256")
PPA_MAPPED_TOOLS = ("yosys_version", "abc_version")


def _compare_ppa(res, rec, got, what, strict, drive_stale=False):
    """A record's `ppa` columns against a fresh weighing `got` (`what` = "rescore" | "recheck"):
    exactly equal when the weighing is the same (`ppa_version`, liberty and pins hashes equal,
    and the same input drive), a note when it cannot be compared (another version, or no liberty
    here: the record is no less valid for that). Under another input drive (`setup.input_drive`:
    the fresh weighing is under the task's drive now, so the task changed it) the A0' columns are
    not compared and the record is `stale` (a note if `drive_stale`: verify_record said so
    already); the A1' columns, which have no driving cell, still are. A record with no numeric
    `ppa` is not compared. `strict`: a fresh weighing that is missing or unavailable is a failure
    (a recheck runs `--ppa require`); otherwise a note (the default rescore must not need the
    liberty)."""
    old = rec.get(PPA_KEY)
    if not (isinstance(old, dict) and old.get("available") is True):
        return
    if not isinstance(got, dict) or got.get("available") is not True:
        why = (got or {}).get("reason", "no `ppa` in the result") if isinstance(got, dict) else "no `ppa` in the result"
        if strict:
            res.fails.append(f"{what}: ppa columns recorded, not weighed now: {why}")
        else:
            res.notes.append(f"ppa columns not re-weighed ({why})")
        return
    other = [k for k in PPA_IDENTITY if old.get(k) != got.get(k)]
    if other:
        res.notes.append(f"ppa columns not compared: recorded under another {', '.join(other)} "
                         "(ppa_version / liberty / pins)")
        return
    od, nd = ppa_input_drive(old), ppa_input_drive(got)
    if od != nd:
        (res.notes if drive_stale else res.stale).append(
            f"{what}: ppa columns not compared: recorded under the input drive {od or '(none named)'}, weighed now "
            f"under {nd or '(none named)'}, the task's: not comparable")
        _compare_mapped(res, old.get(PPA_MAPPED_KEY), got.get(PPA_MAPPED_KEY), what, strict)
        return
    diffs = [f"{what}: ppa.{k} recorded {old.get(k)!r}, now {got.get(k)!r}"
             for k in PPA_COMPARED if old.get(k) != got.get(k)]
    res.fails += diffs
    if not diffs:
        res.notes.append("ppa columns reproduced")
    _compare_mapped(res, old.get(PPA_MAPPED_KEY), got.get(PPA_MAPPED_KEY), what, strict)


def _compare_mapped(res, old, got, what, strict):
    """The `ppa.mapped` columns (flow A1') of a record against a fresh mapping: exactly equal when the mapping is the same
    (version, liberty, mapped pins, script, Yosys and ABC builds equal), a note when it cannot be compared. A record whose design
    the mapping could not weigh (`available: false`), or with no `mapped` object (made before WP-X4), is not compared."""
    if not (isinstance(old, dict) and old.get("available") is True):
        return
    if not isinstance(got, dict) or got.get("available") is not True:
        why = got.get("reason", "no `mapped` in the result") if isinstance(got, dict) else "no `mapped` in the result"
        if strict:
            res.fails.append(f"{what}: ppa.mapped columns recorded, not mapped now: {why}")
        else:
            res.notes.append(f"ppa.mapped columns not re-weighed ({why})")
        return
    other = [k for k in PPA_MAPPED_IDENTITY + PPA_MAPPED_TOOLS if old.get(k) != got.get(k)]
    if other:
        res.notes.append(f"ppa.mapped columns not compared: recorded under another {', '.join(other)}")
        return
    diffs = [f"{what}: ppa.mapped.{k} recorded {old.get(k)!r}, now {got.get(k)!r}"
             for k in PPA_MAPPED_COMPARED if old.get(k) != got.get(k)]
    res.fails += diffs
    if not diffs:
        res.notes.append("ppa.mapped columns reproduced")


# ---------------------------------------------------------------------------
# environment: git, files, subprocesses (not pure)
# ---------------------------------------------------------------------------

def checker_python():
    return os.environ.get("SVGOLF_PYTHON") or shutil.which("python3.12") or sys.executable


def git_revision(path):
    """HEAD of the repository containing `path`, with `+dirty` if the trusted
    base (DIRTY_PATHSPEC) has uncommitted changes; None if git cannot say."""
    try:
        rev = subprocess.run(["git", "-C", path, "rev-parse", "HEAD"], capture_output=True,
                             text=True, check=True).stdout.strip()
        dirty = subprocess.run(["git", "-C", path, "status", "--porcelain", "--"]
                               + list(DIRTY_PATHSPEC), capture_output=True, text=True).stdout.strip()
        return rev + ("+dirty" if dirty else "")
    except (OSError, subprocess.CalledProcessError):
        return None


def statement_files(task, svgolf=SVGOLF):
    """The trusted statement files of `task` (above), relative to `svgolf`, in import order: the module task.json
    `statement.module` names and every svgolf/ module it imports, transitively (read from each file's header,
    `lean_imports`). Raises Refused if the statement module is not a file of `svgolf`."""
    mod = _get(task, "statement", "module")
    if not isinstance(mod, str) or not mod:
        raise Refused([f"task {task.get('name')!r} names no statement module (task.json `statement.module`)"])
    out, todo = [], [mod]
    while todo:
        m = todo.pop(0)
        rel = m.replace(".", "/") + ".lean"
        path = os.path.join(svgolf, rel)
        if rel in out or not os.path.isfile(path):
            if m == mod:
                raise Refused([f"the statement module {mod} is not a file of svgolf/ ({rel})"])
            continue        # outside svgolf/: ls-sv's LeanModels, a package
        out.append(rel)
        with open(path, encoding="utf-8") as fh:
            todo += lean_imports(fh.read())
    return out


def current_statement(task, svgolf=SVGOLF):
    """{file: sha256} of `task`'s trusted statement files as they are now (`statement_files`): what a record's
    `checker.statement` is compared with."""
    return {rel: sha256_file(os.path.join(svgolf, rel)) for rel in statement_files(task, svgolf)}


def current_statement_or_none(task, svgolf=SVGOLF):
    """`current_statement` of `task`, or None (not compared) for no task or a task without a statement module (a
    test's toy task)."""
    if task is None:
        return None
    try:
        return current_statement(task, svgolf)
    except Refused:
        return None


def statement_mismatch(rec, statement):
    """Why `rec` was not checked under `statement` (`current_statement` of its task), or None."""
    got = _get(rec, "checker", "statement")
    if not isinstance(got, dict):
        return "checked before records named the statement they were checked under (2026-11-07)"
    diff = sorted(k for k in set(got) | set(statement) if got.get(k) != statement.get(k))
    if diff:
        return "checked under another statement (" + ", ".join(diff) + " differ)"
    return None


def checker_file_hashes(svgolf=SVGOLF):
    out = {}
    for rel in CHECKER_FILES:
        p = os.path.join(svgolf, rel)
        if os.path.isfile(p):
            out[rel] = sha256_file(p)
    return out


def collect_environment(svgolf=SVGOLF, task=None):
    tc = os.path.join(svgolf, "lean-toolchain")
    toolchain = None
    if os.path.isfile(tc):
        with open(tc, encoding="utf-8") as fh:
            toolchain = fh.read().strip() or None
    env = {"svgolf_revision": git_revision(svgolf), "lean_toolchain": toolchain,
           "files": checker_file_hashes(svgolf)}
    if task is not None:
        try:
            env["statement"] = current_statement(task, svgolf)
        except Refused:
            env["statement"] = None        # a task without a statement module (a test's toy task): none recorded
    return env


def current_flow(svgolf=SVGOLF, flow=COMB_FLOW):
    """The pinned flow `flow` ("comb" or "seq", FLOW_FILES) as it is now: its name, the sha256 of canon.ys and of
    the flow's script and GE table (svgolf.ys and ge.json, or svgolf_seq.ys and ge_seq.json), and Yosys's version
    line (None if Yosys cannot be run). A record is compared with the flow of its task's kind (`task_flow`)."""
    sc = os.path.join(svgolf, "score")
    script, table = FLOW_FILES[flow]
    yosys = os.environ.get("SVGOLF_YOSYS") or "yosys"
    try:
        ver = subprocess.run([yosys, "-V"], capture_output=True, text=True,
                             check=True).stdout.strip() or None
    except (OSError, subprocess.CalledProcessError):
        ver = None

    def sha(name):
        p = os.path.join(sc, name)
        return sha256_file(p) if os.path.isfile(p) else None

    return {"flow": flow, "yosys": ver, "canon_script_sha256": sha("canon.ys"),
            "script_sha256": sha(script), "ge_table_sha256": sha(table)}


def current_flows(svgolf=SVGOLF):
    """{flow name: `current_flow(svgolf, name)`} for every flow of FLOW_FILES."""
    return {name: current_flow(svgolf, name) for name in FLOW_FILES}


def run_check(task_dir, sv, lean, *, check_py=CHECK_PY, lean_wrap=None,
              postsynth=DEFAULT_POSTSYNTH_MODE, ppa=OFFICIAL_PPA_MODE, sandbox=OFFICIAL_SANDBOX_MODE):
    """check.py on one submission; returns (exit status, result JSON). Raises
    RuntimeError if it produced no JSON. check.py runs with `--postsynth
    <postsynth>`: the leaderboard's artifacts are FULL unless a light record
    was asked for (check.py's own default, light, is for local feedback); and with
    `--ppa require`: the sky130 PPA columns are part of an official artifact, so an
    absent liberty is an infrastructure error (exit status 2: never a verdict, never
    a record), not a record without the columns. And with `--sandbox require` (WP-S): the submission's
    Lean, the extractor, Yosys and Verilator run under the OS sandbox, or the check is an infrastructure
    error."""
    env = dict(os.environ)
    if lean_wrap is not None:
        env["SVGOLF_LEAN_WRAP"] = lean_wrap
    proc = subprocess.run([checker_python(), check_py, task_dir, sv, lean, "--sandbox", sandbox,
                           "--ppa", ppa, "--postsynth", postsynth], capture_output=True, text=True, env=env)
    try:
        return proc.returncode, json.loads(proc.stdout)
    except ValueError:
        raise RuntimeError(f"check.py (exit {proc.returncode}) printed no JSON:\n"
                           + (proc.stdout + proc.stderr)[-1500:])


def run_rescore(sv, task_dir, *, score_py=SCORE_PY, timeout=3600, ppa_py=None, mapped=True, seq=False):
    """score.py on the stored design at the task's scoring point. With `ppa_py` (score/ppa.py,
    for a record that carries PPA columns) the same pinned flow runs ONCE through ppa.py, whose
    `score` is score.py's result unchanged, and the result carries the weighed columns as
    `ppa`; if ppa.py cannot weigh (the pinned liberty is absent here, say), score.py runs
    alone and `ppa` is `{"available": false, "reason": ...}`: the rescore itself never
    depends on the liberty. `mapped` False passes `--no-mapped` (no flow A1' mapping, for a
    record that has no mapped columns to reproduce). `seq` (a clocked record, `checker.flow`
    "seq") passes `--seq` to both: the clocked flow, svgolf_seq.ys and ge_seq.json (ppa.py maps
    nothing then)."""
    flow_arg = ["--seq"] if seq else []
    if ppa_py:
        proc = subprocess.run([checker_python(), ppa_py, sv, "--task", task_dir] + flow_arg
                              + ([] if mapped and not seq else ["--no-mapped"]),
                              capture_output=True, text=True, timeout=timeout)
        try:
            out = json.loads(proc.stdout)
        except ValueError:
            out = {}
        if proc.returncode == 0 and "score" in out and "ppa" in out:
            return dict(out["score"], ppa=dict(out["ppa"], available=True))
        why = " ".join(str(out.get("error", proc.stderr[-300:] or proc.returncode)).split())
        return dict(run_rescore(sv, task_dir, score_py=score_py, timeout=timeout, seq=seq),
                    ppa={"available": False, "reason": why[:400]})
    proc = subprocess.run([checker_python(), score_py, sv, "--task", task_dir] + flow_arg,
                          capture_output=True, text=True, timeout=timeout)
    try:
        out = json.loads(proc.stdout)
    except ValueError:
        raise RuntimeError("score.py printed no JSON:\n" + (proc.stdout + proc.stderr)[-1000:])
    if proc.returncode != 0 or "error" in out:
        raise RuntimeError(str(out.get("error", proc.returncode))[:400])
    return out


def today_utc():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")


# ---------------------------------------------------------------------------
# commands
# ---------------------------------------------------------------------------

# a task's name: its directory under tasks/ (never a path: `../x` or `a/../b` is no task)
TASK_NAME_RE = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_-]{0,63}")


def load_task(tasks_dir, name):
    if not isinstance(name, str) or not TASK_NAME_RE.fullmatch(name):
        raise FileNotFoundError(f"no such task: {name!r} (a task is named by its directory under tasks/: letters, "
                                "digits, `_` and `-`)")
    path = os.path.join(tasks_dir, name, "task.json")
    if not os.path.isfile(path):
        raise FileNotFoundError(f"no such task: {name} ({path})")
    with open(path, encoding="utf-8") as fh:
        task = json.load(fh)
    bad = task_leaderboard_problems(task)
    if bad:
        raise ValueError(f"{path}: " + "; ".join(bad))
    return task


def all_task_names(tasks_dir):
    return sorted(t for t in os.listdir(tasks_dir)
                  if os.path.isfile(os.path.join(tasks_dir, t, "task.json")))


RESERVED_HANDLE = (f"the handle `{REFERENCE_PLAYER}` is the proved references' own (their records are par, not "
                   "entries; `seed-references` makes them): a player's record needs a handle of its own")


def add_submission(args, *, sv, lean, player, assisted_by, notes, date, from_check=None, reference=False):
    """Check (or read the result of) one submission and record it. Returns the
    record's path. Raises Refused (not accepted / malformed / duplicate) or
    RuntimeError (infrastructure). Only `seed-references` (`reference`) records
    under REFERENCE_PLAYER (decided 2026-11-12)."""
    task = load_task(args.tasks_dir, args.task)
    mode = getattr(args, "postsynth", None) or DEFAULT_POSTSYNTH_MODE
    # The board's own data directory takes only a record whose kernel check `add` ran itself, in the sandbox: a
    # stored result (`--from-check`) and an unsandboxed run (`--sandbox off`) are for a `--data-dir` trial
    official = is_official_data_dir(args.data_dir)
    if official and from_check:
        raise Refused(["--from-check records a stored check.py result without running the check: the board's own "
                       "data directory (leaderboard/data) takes only a record whose check `add` runs itself (use "
                       "--data-dir DIR for a trial with a stored result)"])
    if official and getattr(args, "sandbox", OFFICIAL_SANDBOX_MODE) == "off":
        raise Refused(["--sandbox off: the board's own data directory (leaderboard/data) takes only a record whose "
                       "check ran in the OS sandbox (use --data-dir DIR for an unsandboxed trial)"])
    with open(sv, "rb") as fh:
        sv_bytes = fh.read()
    with open(lean, "rb") as fh:
        lean_bytes = fh.read()
    task_dir = os.path.join(args.tasks_dir, args.task)
    # Fail fast, before minutes of Lean: malformed human fields, and a duplicate.
    problems = []
    for fn, arg in ((normalize_player, player), (normalize_assisted_by, assisted_by),
                    (normalize_notes, notes), (normalize_date, date)):
        try:
            fn(arg)
        except Refused as e:
            problems += e.problems
    if player == REFERENCE_PLAYER and not reference:
        problems.append(RESERVED_HANDLE)
    if problems:
        raise Refused(problems)
    for _, other, _ in load_records(args.data_dir, args.task):
        if (isinstance(other, dict) and other.get("player") == player
                and _get(other, "files", "sv", "sha256") == sha256_bytes(sv_bytes)
                and _get(other, "files", "lean", "sha256") == sha256_bytes(lean_bytes)):
            raise Refused([f"already recorded: {other.get('record_hash')} (same player, same "
                           "files)"])
    env_before = collect_environment(task=task)    # read BEFORE the check: the checker and the statement as it ran
    if from_check:
        with open(from_check, encoding="utf-8") as fh:
            res = json.load(fh)
    else:
        # check.py reads a snapshot of exactly the bytes that are hashed and stored
        with tempfile.TemporaryDirectory(prefix="svgolf-lb-") as snap:
            sv_snap = os.path.join(snap, os.path.basename(sv))
            lean_snap = os.path.join(snap, os.path.basename(lean))
            with open(sv_snap, "wb") as fh:
                fh.write(sv_bytes)
            with open(lean_snap, "wb") as fh:
                fh.write(lean_bytes)
            rc, res = run_check(task_dir, sv_snap, lean_snap, check_py=args.check_py,
                                lean_wrap=args.lean_wrap, postsynth=mode, sandbox=args.sandbox)
        if rc == 2 or res.get("stage") == "infrastructure":
            raise RuntimeError("check.py reports an infrastructure error (not a verdict on the "
                               "submission): " + str((res.get("errors") or ["?"])[0])[:600])
        env_after = collect_environment(task=task)
        changed = sorted(k for k, v in env_after["files"].items() if env_before["files"].get(k) != v)
        changed += sorted(k for k, v in (env_after.get("statement") or {}).items()
                          if (env_before.get("statement") or {}).get(k) != v)
        if changed:
            raise Refused([f"checker or statement files changed while the check ran ({', '.join(changed)}): "
                           "the result cannot be attributed to one checker; run it again"])
        if official and (res.get("sandbox") or {}).get("active") is not True:
            raise Refused(["the check did not run in the OS sandbox (`sandbox.active` is not true; `--sandbox auto` "
                           "on a machine without a working mechanism): the board's own data directory "
                           "(leaderboard/data) takes only a sandboxed check (use --data-dir DIR for a trial)"])
    rec = build_record(task, res, player=player, assisted_by=assisted_by, notes=notes,
                       submitted_at=date, sv_name=sv, sv_bytes=sv_bytes, lean_name=lean,
                       lean_bytes=lean_bytes, environment=env_before, postsynth=mode)
    if args.require_clean:
        dirty = [k for k in ("svgolf_revision", "lean_surfaces_revision")
                 if not rec["checker"][k] or str(rec["checker"][k]).endswith("+dirty")]
        if dirty:
            raise Refused([f"--require-clean: {dirty} unknown or dirty in "
                           f"{ {k: rec['checker'][k] for k in dirty} }"])
    return store_record(args.data_dir, rec, sv_bytes, lean_bytes)


def is_official_data_dir(data_dir):
    """Whether `data_dir` is the board's own data directory, `leaderboard/data` (DEFAULT_DATA), by real path."""
    return os.path.realpath(data_dir) == os.path.realpath(DEFAULT_DATA)


def cmd_add(args):
    try:
        path = add_submission(args, sv=args.sv, lean=args.lean, player=args.player,
                              assisted_by=args.assisted_by, notes=args.notes,
                              date=args.date or today_utc(), from_check=args.from_check)
    except Refused as e:
        print("REFUSED: the submission was not added:", file=sys.stderr)
        for p in e.problems:
            print(f"  - {p}", file=sys.stderr)
        return 1
    except (RuntimeError, OSError, ValueError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    with open(path, encoding="utf-8") as fh:
        rec = json.load(fh)
    print(f"added {args.task}/{rec['record_hash'][:12]}: {rec['player']}, {score_text(rec)}, "
          f"{rec['proof']['lines']} proof lines -> {os.path.relpath(path)}")
    ps = rec["postsynth"]
    if record_flow(rec) == SEQ_FLOW:
        pts = ps["points"]
        print(f"  post-synthesis check (clocked): {record_mode(ps)} mode at {len(pts)} point(s), "
              + ", ".join(f"{q['point']} ({len(q['seeds'])} seeds, {sum(s['cycles'] for s in q['seeds'])} cycles)"
                          for q in pts) + ", 0 mismatches"
              + ("; a LIGHT record, marked so on the board, for local use: an official record needs `add` without "
                 "`--postsynth light` (the full check)" if record_mode(ps) == "light" else ""))
    elif record_mode(ps) == "light":
        print(f"  NOTE: the post-synthesis check ran in LIGHT mode ({ps['vectors']} of "
              f"{ps.get('full_vectors', ps['vectors'])} vectors): this is a light record, marked "
              "so on the board, for local use; an official record needs `add` without "
              "`--postsynth light` (the full check)")
    else:
        print(f"  post-synthesis check: full mode ({ps['vectors']} vectors)")
    pb = rec.get(PPA_KEY)
    if isinstance(pb, dict) and pb.get("available") is True:
        cols = ranked_columns(rec)
        exact = combined.of_record(rec)
        print(f"  the ranked sky130 score (A0', {pb['ppa_version']}): {pb['area_um2_sky130']} um^2, "
              f"{fmt_time(cols)} ps" + (f" (area x time {combined.um2ns(exact):.2f} {combined.UNIT_ASCII})"
                                        if exact is not None else "")
              + f"; input drive {ppa_input_drive(pb) or '(none named)'}")
        mb = pb.get(PPA_MAPPED_KEY)
        if isinstance(mb, dict) and mb.get("available") is True:
            print(f"  sky130 mapped columns (A1', real abc -liberty; extra and unranked): "
                  f"{mb['area_um2_sky130_mapped_v1']} um^2, {mb['mapped_delay_sky130_v1']} ps, "
                  f"{mb['mapped_cells_sky130_v1']} cells ({mb['ppa_mapped_version']})")
        elif isinstance(mb, dict):
            print(f"  NOTE: the sky130 mapped (A1') columns were not computed: {mb.get('reason')}")
    elif isinstance(pb, dict):
        print(f"  NOTE: the sky130 columns were not computed: {pb.get('reason')}; the record is not ranked")
    else:
        print("  NOTE: this record carries no sky130 columns (the check result has no `ppa` key: "
              "`check.py --ppa off`, or a checker from before them): the boards rank the sky130 score, "
              "so it is NOT RANKED until it is backfilled (checked again with `--ppa require`)")
    # the ASAP7 view (decided 2026-11-09) ranks a record once its columns are measured beside it
    print(f"  NOTE: the site's ASAP7 view ranks it once its ASAP7 columns are measured: "
          f"`leaderboard.py asap7 --write --task {args.task}` (leaderboard/asap7/{args.task}.json)")
    return 0


def score_text(rec):
    """'112.0896 um^2, 1234 ps (112.000 GE, depth 33)': the ranked sky130 score, then the GE columns."""
    cols = ranked_columns(rec)
    ge = f"{fmt_ge(rec['score']['area_mge'])} GE, depth {rec['score']['depth']}"
    if not cols or not has_ranked_columns(cols):
        return f"no sky130 score ({ge})"
    return f"{fmt_um2(cols['area_e4um2'])} um^2, {fmt_time(cols)} ps ({ge})"


def cmd_seed_references(args):
    names = [args.task] if args.task else all_task_names(args.tasks_dir)
    only = set(getattr(args, "ref", None) or [])
    if only and not args.task:
        print("error: --ref needs --task", file=sys.stderr)
        return 2
    status = 0
    for name in names:
        task = load_task(args.tasks_dir, name)
        refs = task.get("references") or []
        stems = {os.path.splitext(os.path.basename(r["sv"]))[0] for r in refs}
        if only - stems:
            print(f"error: {name} has no reference {sorted(only - stems)} (its references: {sorted(stems)})",
                  file=sys.stderr)
            return 2
        for ref in refs:
            if only and os.path.splitext(os.path.basename(ref["sv"]))[0] not in only:
                continue
            sv = os.path.join(args.tasks_dir, name, ref["sv"])
            lean = os.path.join(args.tasks_dir, name, ref["lean"])
            args.task = name
            try:
                path = add_submission(args, sv=sv, lean=lean, player=REFERENCE_PLAYER,
                                      assisted_by=["Claude (Anthropic)"],
                                      notes="reference solution", date=args.date or today_utc(), reference=True)
                print(f"seeded {name}: {ref['sv']} -> {os.path.relpath(path)}")
            except Refused as e:
                print(f"{name}: {ref['sv']}: not added: " + "; ".join(e.problems))
                if not any(p.startswith("already recorded") for p in e.problems):
                    status = 1
            except (RuntimeError, OSError, ValueError) as e:
                print(f"{name}: {ref['sv']}: error: {e}", file=sys.stderr)
                return 2
    return status


def verify_context():
    """What `verify_one` compares every record with, read once per run: the current flows, the checker's files, the
    sky130 and ASAP7 identities, and the ASAP7 tables as they are read (task -> (table, error))."""
    return {"flows": current_flows(), "files": checker_file_hashes(), "identity": ppa_identity(),
            "a7_identity": asap7_identity(), "a7_tables": {}}


def verify_one(args, path, rec, ctx):
    """`verify` of one stored record (a dict) at the level `args` asks for (`args.offline`, `args.full`), against
    `ctx` (`verify_context`): the VerifyResult."""
    task = None
    try:
        task = load_task(args.tasks_dir, rec.get("task", ""))
    except (FileNotFoundError, ValueError):
        pass
    task_dir = os.path.join(args.tasks_dir, rec.get("task", ""))
    has_ppa = (isinstance(rec.get(PPA_KEY), dict) and rec[PPA_KEY].get("available") is True)
    # flow A1' maps once more: only a record that HAS mapped columns to reproduce pays for it
    has_mapped = has_ppa and isinstance(rec[PPA_KEY].get(PPA_MAPPED_KEY), dict) \
        and rec[PPA_KEY][PPA_MAPPED_KEY].get("available") is True
    # compared with the current flow of the task's kind (the record's own when the task cannot be read); the
    # rescore runs the record's own flow (`score.py --seq` for a clocked record)
    flow = ctx["flows"][task_flow(task) if task is not None else record_flow(rec)]
    seq = record_flow(rec) == SEQ_FLOW
    rescore = (None if args.offline or args.full or task is None
               else (lambda sv, td=task_dir, w=has_ppa, m=has_mapped, q=seq: run_rescore(
                   sv, td, score_py=args.score_py, ppa_py=args.ppa_py if w else None, mapped=m, seq=q)))
    # a record WITH columns is rechecked under `--ppa require` (the official mode: the columns must
    # reproduce); a record made before them is rechecked as it always was, without needing the liberty
    recheck = (None if not args.full or task is None else
               (lambda sv, lean, td=task_dir, w=has_ppa: run_check(
                   td, sv, lean, check_py=args.check_py, lean_wrap=args.lean_wrap,
                   postsynth="full", ppa=OFFICIAL_PPA_MODE if w else "off", sandbox=args.sandbox)[1]))
    # the ASAP7 view: the record's entry must be bound to it; plain `verify` and `--full` also re-weigh it
    # (ppa.py --pdk asap7; `--full`'s check.py run weighs sky130 only)
    a7 = None
    if task is not None:
        if task["name"] not in ctx["a7_tables"]:
            ctx["a7_tables"][task["name"]] = read_asap7(task["name"], args.asap7_dir)
        table, why = ctx["a7_tables"][task["name"]]
        cyc = (rec.get("score") or {}).get("cycles")
        a7 = {"table": table, "error": why, "identity": ctx["a7_identity"],
              "rescore": None if args.offline else (lambda sv, td=task_dir, q=seq, c=cyc: asap7_columns_of(
                  *run_asap7(sv, td, ppa_py=args.ppa_py, seq=q), c))}
    return verify_record(path, rec, task, flow=flow, current_files=ctx["files"], rescore=rescore,
                         recheck=recheck, ppa_identity=ctx["identity"],
                         ppa_setup=ppa_setup_now(task) if task is not None else None,
                         statement=current_statement_or_none(task), asap7_view=a7)


def verify_line(label, rec, r):
    """`verify`'s line for one record: '[ok] add/8c1f662e6f8c: alice 541.7696 um^2, ...: hashes and arithmetic ok'
    (`label`: the record's path under the data directory)."""
    who = f"{rec.get('player')} {score_text(rec)}" if not validate_record(rec) else "malformed"
    detail = "; ".join(r.fails + r.stale + r.notes)
    task_name, _, stem = label[:-len(".json")].partition(os.sep)
    return f"[{r.status}] {task_name}/{stem[:12]}: {who}: {detail or 'hashes and arithmetic ok'}"


def cmd_verify(args):
    if args.task:
        try:
            load_task(args.tasks_dir, args.task)
        except (FileNotFoundError, ValueError) as e:
            print(f"error: {e}", file=sys.stderr)
            return 2
    loaded = load_records(args.data_dir, args.task)
    if not loaded:
        print("no records")
        return 0
    ctx = verify_context()
    failed = stale = 0
    for path, rec, err in loaded:
        label = os.path.relpath(path, args.data_dir)
        if not isinstance(rec, dict):
            print(f"[FAIL] {label}: not a JSON object" + (f": {err}" if err else ""))
            failed += 1
            continue
        r = verify_one(args, path, rec, ctx)
        print(verify_line(label, rec, r))
        failed += bool(r.fails)
        stale += bool(r.stale) and not r.fails
    level = "offline" if args.offline else ("full re-check" if args.full else "hashes + rescore")
    print(f"verify ({level}): {len(loaded)} records, {failed} failed, {stale} stale")
    return 1 if failed else 0


def _boards(args, names, unassisted=False):
    """The boards of `names`, ranked under the current flow and sky130 identity and each task's input drive
    (`--all-flows`: none of them checked; a record without sky130 columns is never ranked). `--pdk asap7`: the boards
    of the ASAP7 view (leaderboard/asap7/<task>.json, under the current ASAP7 identity unless `--all-flows`)."""
    pdk = getattr(args, "pdk", DEFAULT_PDK)
    flows = None if args.all_flows else current_flows()
    identity = None if args.all_flows else ppa_identity()
    a7_identity = None if args.all_flows else asap7_identity()
    records = good_records(load_records(args.data_dir), warn=lambda m: print(m, file=sys.stderr))
    out = []
    for n in names:
        task = load_task(args.tasks_dir, n)
        flow = None if flows is None else flows[task_flow(task)]      # the current flow of the task's kind
        mine = [r for r in records if r["task"] == n]
        drive = None if args.all_flows else ppa_setup_now(task).get("input_drive")
        statement = None if args.all_flows else current_statement_or_none(task)
        a7 = (load_asap7(n, getattr(args, "asap7_dir", ASAP7_DIR), warn=lambda m: print(m, file=sys.stderr))
              if pdk == "asap7" else None)
        board = build_board(task, mine, flow=flow, unassisted=unassisted, identity=identity, input_drive=drive,
                            statement=statement, pdk=pdk, asap7=a7, asap7_identity=a7_identity)
        # par: the best of the reference player's records that rank here (whatever `unassisted` says: par is the
        # bar, not an entry)
        board["par"] = par_of(task, mine, flow=flow, identity=identity, input_drive=drive,
                              names=reference_names(args.tasks_dir, task), statement=statement, pdk=pdk, asap7=a7,
                              asap7_identity=a7_identity)
        out.append(board)
    return out


def reference_names(tasks_dir, task):
    """design sha256 -> (index, stem) of the proved references task.json lists, the first one for a design
    that two references share (a second proof of one design, `add_n_byhand`); a file that cannot be read is
    left out."""
    out = {}
    for i, ref in enumerate(task.get("references") or []):
        try:
            sha = sha256_file(os.path.join(tasks_dir, task["name"], ref["sv"]))
        except (OSError, KeyError, TypeError):
            continue
        out.setdefault(sha, (i, os.path.splitext(os.path.basename(ref["sv"]))[0]))
    return out


def par_now(task_name, data_dir=DEFAULT_DATA, tasks_dir=DEFAULT_TASKS):
    """PAR of a task as its board shows it now (`par_of` over the records of `data_dir`, under the current
    flow, sky130 identity and the task's input drive), or None. What check.py's ranked headline names."""
    task = load_task(tasks_dir, task_name)
    records = good_records(load_records(data_dir, task_name))
    return par_of(task, records, flow=current_flow(SVGOLF, task_flow(task)), identity=ppa_identity(),
                  input_drive=ppa_setup_now(task).get("input_drive"), names=reference_names(tasks_dir, task),
                  statement=current_statement_or_none(task))


def cmd_pareto_axes(args):
    """`pareto --axes A,B,...`: the opt-in n-D view (see "the n-dimensional Pareto view")."""
    try:
        axes = parse_axes(args.axes)
        task = load_task(args.tasks_dir, args.task)
    except Refused as e:
        print("error: " + "; ".join(e.problems), file=sys.stderr)
        return 2
    except (FileNotFoundError, ValueError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    records = [r for r in good_records(load_records(args.data_dir, args.task),
                                       warn=lambda m: print(m, file=sys.stderr))]
    view = build_axes_view(task, records, axes, flow=None if args.all_flows else current_flow(SVGOLF, task_flow(task)),
                           identity=None if args.all_flows else ppa_identity(),
                           mapped_identity=None if args.all_flows else ppa_mapped_identity(),
                           unassisted=args.unassisted,
                           input_drive=None if args.all_flows else ppa_setup_now(task).get("input_drive"),
                           statement=None if args.all_flows else current_statement_or_none(task))
    print(json.dumps(view, indent=2, sort_keys=True) if args.format == "json"
          else render_axes_text(view))
    return 0


def cmd_pareto(args):
    if getattr(args, "axes", None):
        if getattr(args, "pdk", DEFAULT_PDK) != DEFAULT_PDK:
            print("error: --axes names the records' own (sky130) columns; it does not take --pdk", file=sys.stderr)
            return 2
        return cmd_pareto_axes(args)
    try:
        (board,) = _boards(args, [args.task], args.unassisted)
    except (FileNotFoundError, ValueError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    if args.format == "json":
        # exploration: each frontier row carries its board `rank` and its ranked number (`exact`, `um2ns`)
        print(json.dumps({"task": board["task"], "view": "exploration", "ranked_by": board["ranked_by"],
                          "frontier": board["frontier"]}, indent=2, sort_keys=True))
    else:
        print(render_pareto_text(board))
    return 0


def cmd_board(args):
    try:
        (board,) = _boards(args, [args.task], args.unassisted)
    except (FileNotFoundError, ValueError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    print(json.dumps(board, indent=2, sort_keys=True) if args.format == "json"
          else render_markdown(board, 2))
    return 0


def cmd_export(args):
    try:
        boards = _boards(args, all_task_names(args.tasks_dir))
    except (FileNotFoundError, ValueError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    with open(args.out, "w", encoding="utf-8") as fh:
        fh.write(render_export(boards, getattr(args, "pdk", DEFAULT_PDK)))
    print(f"wrote {args.out}: {len(boards)} tasks, "
          f"{sum(len(b['ranking']) for b in boards)} ranked records")
    return 0


def cmd_asap7(args):
    """`asap7`: the ASAP7 view's columns (see "the ASAP7 view"). Exit 0 all good, 1 a check or a measurement failed,
    2 usage or infrastructure."""
    names = [args.task] if args.task else all_task_names(args.tasks_dir)
    try:
        with open(EXPECTED_JSON, encoding="utf-8") as fh:
            expected = json.load(fh)
        tasks = {n: load_task(args.tasks_dir, n) for n in names}
    except (OSError, ValueError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    identity = asap7_identity()
    if identity is None:
        print(f"error: {os.path.relpath(PPA_PINS_ASAP7, SVGOLF)} cannot be read", file=sys.stderr)
        return 2
    records = good_records(load_records(args.data_dir), warn=lambda m: print(m, file=sys.stderr))
    status = 0
    for name in names:
        task = tasks[name]
        designs = asap7_designs(task, records, expected, tasks_dir=args.tasks_dir, data_dir=args.data_dir)
        if not designs:
            continue
        seq = task_flow(task) == SEQ_FLOW
        task_dir = os.path.join(args.tasks_dir, name)
        flow = current_flow(SVGOLF, task_flow(task))

        def weigh(sv, cycles, td=task_dir, q=seq):
            return asap7_columns_of(*run_asap7(sv, td, ppa_py=args.ppa_py, seq=q), cycles)
        path = asap7_path(name, args.asap7_dir)
        if args.write:
            bad, entries, script = [], [], None
            for sha in sorted(designs):
                d = designs[sha]
                if d["conflicts"]:
                    bad += [f"{', '.join(d['of'])}: {c}" for c in d["conflicts"]]
                    continue
                try:
                    score, ppa = run_asap7(d["src"], task_dir, ppa_py=args.ppa_py, seq=seq)
                    cols = asap7_columns_of(score, ppa, d["want"].get("cycles"))
                except (RuntimeError, OSError, KeyError, subprocess.TimeoutExpired) as e:
                    print(f"error: {name}: {', '.join(d['of'])}: {e}", file=sys.stderr)
                    return 2
                if score.get("params") != scoring_point(task):
                    bad.append(f"{', '.join(d['of'])}: weighed at {score.get('params')}, not at {scoring_point(task)}")
                if any(ppa.get(k) != identity.get(k) for k in ASAP7_IDENTITY if k != "input_drive") \
                        or (ppa.get("setup") or {}).get("input_drive") != identity["input_drive"]:
                    bad.append(f"{', '.join(d['of'])}: weighed under another ASAP7 identity than the pins file's")
                if sha256_file(d["src"]) != sha:
                    bad.append(f"{', '.join(d['of'])}: the design file changed while it was weighed")
                bad += [f"{', '.join(d['of'])}: {p}" for p in asap7_want_problems(cols, d["want"])]
                script = script or ppa.get("ppa_script_sha256")
                entries.append(dict(cols, sv_sha256=sha, of=d["of"]))
            if bad:
                print(f"[FAIL] {name}: not written: " + "; ".join(bad))
                status = 1
                continue
            data = {"_comment": ("GENERATED by `leaderboard.py asap7 --write`; do not edit (measure again instead). "
                                 "The ASAP7 view's columns (decided 2026-11-09): score/ppa.py --pdk asap7 --no-mapped "
                                 "(flow A0', asap7_a0_v1) on every design the task's pages show at its scoring point, "
                                 "one entry per design file, bound to the sky130 side by the canonical text, RTLIL, GE "
                                 "columns, cycles and scored netlist. Areas in 1e-5 um^2, times in ps (time = cycles x "
                                 "delay on a clocked task, the delay being the register-to-register period). Derived "
                                 "data, outside every record hash; `leaderboard.py verify` and `asap7 --rescore` "
                                 "re-derive it. See leaderboard/README.md, \"The ASAP7 view\"."),
                    "schema": ASAP7_SCHEMA, "task": name, "scoring_point": scoring_point(task), "flow": flow,
                    "identity": identity, "ppa_script_sha256": script, "designs": entries}
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(json.dumps(data, indent=1, sort_keys=True) + "\n")
            print(f"[ok] {name}: wrote {os.path.relpath(path)} ({len(entries)} designs)")
            continue
        table, why = read_asap7(name, args.asap7_dir)
        if why or table is None:
            print(f"[FAIL] {name}: {why or f'no {os.path.relpath(path, SVGOLF)}: `asap7 --write` measures it'}")
            status = 1
            continue
        rescore = (lambda e, d, w=weigh: w(d["src"], d["want"].get("cycles"))) if args.rescore else None
        fails, notes = asap7_check(task, table, designs, identity=identity, flow=flow, rescore=rescore)
        tag = "FAIL" if fails else ("stale" if notes and any("not comparable" in n for n in notes) else "ok")
        what = "re-weighed, every column reproduced" if args.rescore and not fails else "bound to every design"
        print(f"[{tag}] {name}: {len(table['designs'])} designs: " + ("; ".join(fails + notes) or what))
        status = status or (1 if fails else 0)
    return status


# ---------------------------------------------------------------------------
# handing a record in: `submit` (decided 2026-11-11)
# ---------------------------------------------------------------------------
# A record reaches the public board by a pull request that adds its three files (README.md, "Leaderboard"). `submit`
# opens it with the player's own git and GitHub command-line tool (`gh`, and its login): it checks the record at the
# offline level first, makes a commit of the three files on the public repository's main branch WITHOUT touching the
# player's working tree, index or branches (a temporary index; only git objects are written), pushes it to a branch of
# the player's fork and opens the pull request, whose text names the task, the handle, `assisted_by` and the record's
# board line. `--dry-run` prints the commands and the text and changes nothing; without `gh` it prints the steps to do
# by hand. The check every such pull request gets is leaderboard/pr_check.py.

SUBMIT_BRANCH = "main"            # the public repository's branch a record's pull request goes to
SITE_CONFIG = os.path.join(SVGOLF, "site", "config.json")      # its `repo_url`: the public repository, or null
# an owner is a letter or digit and up to 38 more of them or `-`; a repository is no `.` or `..`
GITHUB_REPO_RE = re.compile(r"https://github\.com/([A-Za-z0-9][A-Za-z0-9-]{0,38})/(?!\.\.?(?:\.git)?/?$)"
                            r"([A-Za-z0-9_.-]+?)(?:\.git)?/?")
RECORD_PREFIX_RE = re.compile(r"[0-9a-f]{12,64}")
# The parts of a record's pull request, in order: `submit_text` writes them, and .github/pull_request_template.md has
# the same headings (a test compares them)
PR_HEADINGS = ("Record", "Board line", "Checks")
PR_CHECK_NOTE = ("The check on this pull request runs `leaderboard.py verify --offline` on every record and the full "
                 "check (`verify --full`) on the records it adds, and writes their board lines to its summary. A "
                 "maintainer re-makes the ranked number on the rating build when the pull request is merged.")
PR_TEXT_END = "SVGOLF_PR_TEXT"    # the here-document delimiter of the printed steps


def pinned_flows(path=EXPECTED_JSON):
    """The rating build's flows as tests/expected.json pins them, {flow name: {yosys, canon_script_sha256,
    script_sha256, ge_table_sha256}}: what the site ranks the records under (site/build.py `collect`), whatever Yosys
    this machine has. Raises OSError or ValueError (KeyError) if the file cannot be read."""
    with open(path, encoding="utf-8") as fh:
        expected = json.load(fh)
    out = {}
    for name, key in ((COMB_FLOW, "flow"), (SEQ_FLOW, "flow_seq")):
        pin = expected.get(key)
        if isinstance(pin, dict):
            out[name] = {"yosys": pin["yosys_version"], "canon_script_sha256": pin["canon_script_sha256"],
                         "script_sha256": pin["script_sha256"], "ge_table_sha256": pin["ge_table_sha256"]}
    return out


def board_now(task, data_dir, tasks_dir=DEFAULT_TASKS, flows=None):
    """`task`'s board and par as the site shows them (site/build.py `collect_task`): the players' intact records of
    `data_dir` (the reference player's are par, not entries), ranked under the rating build's pinned flow of the
    task's kind (`pinned_flows`, or `flows`), the current sky130 identity and the task's input drive and statement now.
    Returns (board, par). Raises ValueError when no flow of the task's kind is pinned."""
    flows = pinned_flows() if flows is None else flows
    flow = flows.get(task_flow(task))
    if flow is None:
        raise ValueError(f"tests/expected.json pins no {task_flow(task)} flow (task {task['name']})")
    records = good_records(load_records(data_dir, task["name"]))
    kw = dict(flow=flow, identity=ppa_identity(), input_drive=ppa_setup_now(task).get("input_drive"),
              statement=current_statement_or_none(task))
    board = build_board(task, [r for r in records if r["player"] != REFERENCE_PLAYER], **kw)
    return board, par_of(task, records, names=reference_names(tasks_dir, task), **kw)


def board_line(board, par, record_hash):
    """One record's place on its task's board (`board_now`'s board and par), as one line of Markdown: its area x time
    and its rank among the players' records, whether it is under par, and par; or why it is not ranked. Pure."""
    head = f"`{board['task']}` record `{record_hash[:12]}`"
    row = next((r for r in board["ranking"] if r["record_hash"] == record_hash), None)
    if row is not None:
        line = (f"{head} by `{row['player']}`: {fmt_area(row)} um^2 x {fmt_time(row)} ps = {fmt_adp(row)} "
                f"{combined.UNIT_ASCII}, rank {row['rank']} of {len(board['ranking'])}")
        if par is None:
            return line + "; par: none recorded"
        return line + ("; under par" if row["exact"] < par["exact"] else "; not under par") + "; par " + fmt_par(par)
    row = next((r for r in board["unranked"] if r["record_hash"] == record_hash), None)
    if row is not None:
        return f"{head} by `{row['player']}`: not ranked: {row['reason']}"
    return (f"{head}: not on the board (no intact player's record of that hash for this task; the proved "
            "references' records are par, not entries)")


def find_record(data_dir, task_name, prefix):
    """(path, record) of the one record of `task_name` in `data_dir` whose hash starts with `prefix` (12 to 64 hex
    characters: `add` prints 12). Raises Refused when there is none, or several, or the file is not a JSON object."""
    if not RECORD_PREFIX_RE.fullmatch(prefix or ""):
        raise Refused([f"--record {prefix!r}: the record's hash, or its first 12 characters or more, as `add` prints "
                       "it"])
    hits = [(p, r, e) for p, r, e in load_records(data_dir, task_name) if os.path.basename(p).startswith(prefix)]
    where = os.path.join(os.path.relpath(data_dir), task_name)
    if not hits:
        raise Refused([f"no record {prefix} of task {task_name} in {where}"])
    if len(hits) > 1:
        raise Refused([f"{prefix} names {len(hits)} records of task {task_name}: give more of the hash"])
    path, rec, err = hits[0]
    if not isinstance(rec, dict):
        raise Refused([f"{os.path.relpath(path)} is not a JSON object" + (f": {err}" if err else "")])
    return path, rec


def submit_text(rec, line, verified):
    """The title and the text (Markdown) of `rec`'s pull request: the task, the handle, `assisted_by` and the files
    (Record), `line` (`board_line`), and `verified` (`verify_line` of the offline check `submit` ran) with what the
    pull request's own check does (Checks). The headings are PR_HEADINGS. Pure."""
    row = row_of(rec)
    score = (f"{fmt_area(row)} um^2 x {fmt_time(row)} ps = {fmt_adp(row)} {combined.UNIT_ASCII}"
             if row["exact"] is not None else "no sky130 score")
    title = f"record {rec['task']} {rec['player']} {rec['record_hash'][:12]}: {score}"
    files = f"leaderboard/data/{rec['task']}/{rec['record_hash']}"
    assisted = "; ".join(md_escape(a) for a in rec["assisted_by"]) if rec["assisted_by"] else "none (unassisted)"
    body = [f"## {PR_HEADINGS[0]}", "", f"- task: `{rec['task']}`", f"- handle: `{rec['player']}`",
            f"- assisted by: {assisted}", f"- files: `{files}.json`, `.sv` and `.lean`, as `leaderboard.py add` wrote "
            "them", "",
            f"## {PR_HEADINGS[1]}", "", line, "",
            f"## {PR_HEADINGS[2]}", "", "`leaderboard.py verify --offline` of this record before it was sent:", "",
            "```text", verified, "```", "", PR_CHECK_NOTE, ""]
    return title, "\n".join(body)


def submit_steps(rec, root, files, owner, repo, title):
    """The steps of `submit` for `rec`, in order, each {"var", "argv", "index", "gh"}: `argv` (with `$NAME` for the
    output of an earlier step), `var` the name its output is kept under (or None), `index` whether it runs with
    GIT_INDEX_FILE=$TMP/index (a temporary index, so the player's own index, working tree and branches are never
    touched), `gh` whether it needs the GitHub command-line tool. Two steps are not commands: TMP (a new temporary
    directory) and BODY (the pull request's text written to $TMP/body.md). `root`: the svgolf directory as `git -C`
    names it; `files`: the record's .json, .sv and .lean as paths from `root`; `owner`/`repo`: the public repository on
    GitHub. Pure."""
    task, h = rec["task"], rec["record_hash"]
    branch = f"record-{task}-{h[:12]}"
    git = ["git", "-C", root]
    names = [f"leaderboard/data/{task}/{h}{ext}" for ext in (".json", ".sv", ".lean")]
    blobs = ("JSON", "SV", "LEAN")
    step = lambda var, argv, index=False, gh=False: {"var": var, "argv": argv, "index": index, "gh": gh}  # noqa: E731
    out = [step("TMP", ["mktemp", "-d"]), step("BODY", []),
           step(None, git + ["fetch", "--no-tags", f"https://github.com/{owner}/{repo}.git", SUBMIT_BRANCH]),
           step("BASE", git + ["rev-parse", "FETCH_HEAD"])]
    out += [step(b, git + ["hash-object", "-w", "--", f]) for b, f in zip(blobs, files)]
    out += [step(None, git + ["read-tree", "$BASE"], index=True),
            step(None, git + ["update-index", "--add"]
                 + [x for b, n in zip(blobs, names) for x in ("--cacheinfo", f"100644,${b},{n}")], index=True),
            step("TREE", git + ["write-tree"], index=True),
            step("COMMIT", git + ["commit-tree", "$TREE", "-p", "$BASE", "-m", title]),
            step(None, ["gh", "repo", "fork", f"{owner}/{repo}", "--clone=false", "--remote=false"], gh=True),
            step("LOGIN", ["gh", "api", "user", "--jq", ".login"], gh=True),
            step(None, git + ["push", f"https://github.com/$LOGIN/{repo}.git", f"$COMMIT:refs/heads/{branch}"]),
            step(None, ["gh", "pr", "create", "--repo", f"{owner}/{repo}", "--base", SUBMIT_BRANCH, "--head",
                        f"$LOGIN:{branch}", "--title", title, "--body-file", "$TMP/body.md"], gh=True)]
    return out


# a word that may stand in double quotes: `$` only as an earlier step's output ($NAME), and none of `"`, `\`, `` ` ``, `!`
SHELL_DQ_SAFE = re.compile(r'(?:[^"\\`$!]|\$[A-Z]+)*')


def _shell_word(w):
    """One word of a printed command: double-quoted when it names an earlier step's output ($NAME) and holds nothing
    else the shell would read inside double quotes, else quoted as the shell needs (`shlex.quote`: nothing in it
    expands)."""
    return f'"{w}"' if "$" in w and SHELL_DQ_SAFE.fullmatch(w) else shlex.quote(w)


def submit_script(steps, body, manual=False, owner="", repo=""):
    """The steps as a shell script (what `--dry-run` prints). `manual`: without the GitHub command-line tool, its
    three steps become what to do on github.com, and LOGIN is typed by hand. Pure."""
    out = []
    for st in steps:
        if st["var"] == "TMP":
            out.append("TMP=$(mktemp -d)")
        elif st["var"] == "BODY":
            out += [f"cat > \"$TMP/body.md\" <<'{PR_TEXT_END}'", body.rstrip("\n"), PR_TEXT_END]
        elif manual and st["gh"]:
            if st["var"] == "LOGIN":
                out += [f"# fork https://github.com/{owner}/{repo} on github.com (once), then:",
                        "LOGIN=YOUR_GITHUB_LOGIN"]
            elif "create" in st["argv"]:
                branch = st["argv"][st["argv"].index("--head") + 1].split(":", 1)[1]
                out += [f"# open https://github.com/{owner}/{repo}/compare/{SUBMIT_BRANCH}...$LOGIN:{branch}?expand=1,",
                        "# give it the title of the commit and the text of $TMP/body.md (above), and create it"]
        else:
            cmd = ('GIT_INDEX_FILE="$TMP/index" ' if st["index"] else "") + " ".join(_shell_word(w) for w in st["argv"])
            out.append(f"{st['var']}=$({cmd})" if st["var"] else cmd)
    return "\n".join(out) + "\n"


def run_submit_steps(steps, body):
    """Run `submit_steps`' steps; returns the last command's output (`gh pr create` prints the pull request's
    address). Raises RuntimeError naming the step that failed; the temporary directory is removed either way."""
    names = {}

    def fill(w):
        return re.sub(r"\$([A-Z]+)", lambda m: names.get(m.group(1), m.group(0)), w)
    try:
        out = ""
        for st in steps:
            if st["var"] == "TMP":
                names["TMP"] = tempfile.mkdtemp(prefix="svgolf-submit-")
                continue
            if st["var"] == "BODY":
                with open(os.path.join(names["TMP"], "body.md"), "w", encoding="utf-8") as fh:
                    fh.write(body)
                continue
            argv = [fill(w) for w in st["argv"]]
            env = dict(os.environ)
            if st["index"]:
                env["GIT_INDEX_FILE"] = os.path.join(names["TMP"], "index")
            proc = subprocess.run(argv, capture_output=True, text=True, env=env)
            if proc.returncode != 0:
                hint = (" (git pushes with its own login for github.com: `gh auth setup-git` makes it gh's)"
                        if "push" in argv else "")
                raise RuntimeError(f"`{shlex.join(argv)}` failed (exit {proc.returncode}){hint}: "
                                   + " ".join((proc.stderr or proc.stdout).split())[-600:])
            out = proc.stdout.strip()
            if st["var"]:
                names[st["var"]] = out
        return out
    finally:
        if "TMP" in names:
            shutil.rmtree(names["TMP"], ignore_errors=True)


def site_repo_url(path=SITE_CONFIG):
    """site/config.json's `repo_url`: the public repository, or None (null, or the file cannot be read)."""
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh).get("repo_url")
    except (OSError, ValueError, AttributeError):
        return None


def cmd_submit(args):
    """`submit`: hand a record in (above). Exit 0 the pull request is open, or the steps were printed (`--dry-run`,
    or no `gh`); 1 the record is refused; 2 usage or a step that failed."""
    try:
        task = load_task(args.tasks_dir, args.task)
    except (FileNotFoundError, ValueError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    url = args.repo or site_repo_url()
    m = GITHUB_REPO_RE.fullmatch(url or "")
    if not m:
        print("error: " + (f"--repo {url!r} is not a GitHub repository (https://github.com/OWNER/REPO)" if url else
                           "no public repository is named here (site/config.json `repo_url` is null): pass --repo "
                           "https://github.com/OWNER/REPO"), file=sys.stderr)
        return 2
    owner, repo = m.group(1), m.group(2)
    try:
        if not is_official_data_dir(args.data_dir):
            raise Refused(["submit hands in a record of the board's own data directory, leaderboard/data, where `add` "
                           "writes without --data-dir; a record made with --data-dir is a private trial"])
        path, rec = find_record(args.data_dir, args.task, args.record)
        if rec.get("player") == REFERENCE_PLAYER:
            raise Refused([RESERVED_HANDLE])
        vargs = argparse.Namespace(**vars(args))
        vargs.offline, vargs.full = True, False
        r = verify_one(vargs, path, rec, verify_context())
        verified = verify_line(os.path.relpath(path, args.data_dir), rec, r)
        print(verified)
        problems = list(r.fails) + [f"stale: {s}: the board would not rank it; make it again with `add`"
                                    for s in r.stale]
        if not r.fails and record_mode(rec["postsynth"]) == "light":
            problems.append("a LIGHT record (its post-synthesis check ran light) never ranks: it is for local use; "
                            "`add` without --postsynth light makes one the board ranks")
        if problems:
            raise Refused(problems)
    except Refused as e:
        print("REFUSED: the record was not submitted:", file=sys.stderr)
        for p in e.problems:
            print(f"  - {p}", file=sys.stderr)
        return 1
    try:
        board, par = board_now(task, args.data_dir, args.tasks_dir)
    except (OSError, ValueError) as e:
        print(f"error: the board cannot be built: {e}", file=sys.stderr)
        return 2
    line = board_line(board, par, rec["record_hash"])
    title, body = submit_text(rec, line, verified)
    print(f"board line: {line}")
    files = [os.path.relpath(p, SVGOLF) for p in record_paths(args.data_dir, rec["task"], rec["record_hash"])]
    gh = shutil.which("gh")
    if args.dry_run or not gh:
        steps = submit_steps(rec, os.path.relpath(SVGOLF), files, owner, repo, title)
        print(("submit --dry-run: nothing was changed or sent. The steps, from this directory:" if args.dry_run else
               "submit: the GitHub command-line tool (gh) is not on PATH, so nothing was changed or sent. The steps, "
               "from this directory, by hand:"))
        print(submit_script(steps, body, manual=not gh, owner=owner, repo=repo), end="")
        return 0
    try:
        out = run_submit_steps(submit_steps(rec, SVGOLF, files, owner, repo, title), body)
    except (RuntimeError, OSError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    print(f"opened: {out}")
    return 0


def make_parser():
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--data-dir", default=os.environ.get("SVGOLF_LEADERBOARD_DATA",
                                                             DEFAULT_DATA),
                        help="where the records live (default: leaderboard/data)")
    common.add_argument("--tasks-dir", default=DEFAULT_TASKS, help=argparse.SUPPRESS)
    common.add_argument("--check-py", default=CHECK_PY, help=argparse.SUPPRESS)
    common.add_argument("--score-py", default=SCORE_PY, help=argparse.SUPPRESS)
    common.add_argument("--ppa-py", default=PPA_PY, help=argparse.SUPPRESS)
    common.add_argument("--asap7-dir", default=ASAP7_DIR, help=argparse.SUPPRESS)
    common.add_argument("--sandbox", choices=("off", "auto", "require"), default=OFFICIAL_SANDBOX_MODE,
                        help="check.py's --sandbox for the checks `add` and `verify --full` run (default "
                        "`require`: an official record is made with the OS sandbox or not at all; `off` is refused "
                        "for the board's own data directory, leaderboard/data)")
    common.add_argument("--lean-wrap", default=None,
                        help="command prefix for every lake/lean call (default: "
                        "$SVGOLF_LEAN_WRAP, which check.py reads itself)")
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)

    a = sub.add_parser("add", parents=[common], help="check a submission and record it")
    a.add_argument("--task", required=True)
    a.add_argument("--player", required=True)
    a.add_argument("--assisted-by", action="append", default=[], metavar="TOOL",
                   help="a tool or AI system that helped (repeatable; free text)")
    a.add_argument("--sv", required=True)
    a.add_argument("--lean", required=True)
    a.add_argument("--notes", default="")
    a.add_argument("--from-check", metavar="RESULT.json",
                   help="use this check.py result instead of running check.py (a --data-dir trial only: the "
                   "board's own data directory, leaderboard/data, takes only a check `add` runs itself)")
    a.add_argument("--date", help="submission date YYYY-MM-DD (default: today, UTC)")
    a.add_argument("--require-clean", action="store_true",
                   help="refuse if the svgolf or lean-surfaces revision is unknown or +dirty")
    a.add_argument("--postsynth", choices=POSTSYNTH_MODES, default=DEFAULT_POSTSYNTH_MODE,
                   help="the post-synthesis mode check.py runs in (default: full, the only "
                   "official one). `light` records a LIGHT record, marked so on the board; "
                   "with --from-check it names the mode the stored result may have run in")
    a.set_defaults(fn=cmd_add)

    s = sub.add_parser("seed-references", parents=[common],
                       help="record every proved reference solution (runs check.py on each)")
    s.add_argument("--task")
    s.add_argument("--ref", action="append", default=[], metavar="STEM",
                   help="only this reference of --task (its .sv's stem, e.g. add_n; repeatable)")
    s.add_argument("--date")
    s.add_argument("--require-clean", action="store_true")
    s.set_defaults(fn=cmd_seed_references)

    v = sub.add_parser("verify", parents=[common], help="re-verify stored records")
    v.add_argument("--task")
    g = v.add_mutually_exclusive_group()
    g.add_argument("--offline", action="store_true",
                   help="hashes and arithmetic only: no Yosys, no Lean")
    g.add_argument("--full", action="store_true",
                   help="re-run check.py on every stored submission (hours of Lean), always "
                   "with --postsynth full")
    v.set_defaults(fn=cmd_verify)

    for name, fn, h in (("pareto", cmd_pareto, "the (sky130 area, time) Pareto frontier of a task (exploration: "
                                               "the board ranks area x time)"),
                        ("board", cmd_board, "the ranked board of a task, by area x time")):
        b = sub.add_parser(name, parents=[common], help=h)
        b.add_argument("--task", required=True)
        b.add_argument("--format", choices=("md", "json") if name == "board" else ("text", "json"),
                       default="md" if name == "board" else "text")
        b.add_argument("--unassisted", action="store_true",
                       help="only records with an empty assisted_by")
        b.add_argument("--all-flows", action="store_true",
                       help="rank records checked under another flow too")
        b.add_argument("--pdk", choices=PDKS, default=DEFAULT_PDK,
                       help="the library the board ranks on: sky130 (the default, the records' own columns) or asap7 "
                       "(the ASAP7 view: leaderboard/asap7/<task>.json)")
        if name == "pareto":
            b.add_argument("--axes", metavar="A,B,...",
                           help="opt-in: the n-dimensional Pareto frontier over these axes, for the "
                           "records that carry them (known: " + ", ".join(AXES) + "), e.g. "
                           "--axes area_mge,depth (the GE columns). Without --axes: the frontier of the "
                           "ranked number's two factors (area_um2_sky130, time_ps)")
        b.set_defaults(fn=fn)

    e = sub.add_parser("export", parents=[common], help="all tasks' boards as one Markdown file")
    e.add_argument("--out", required=True)
    e.add_argument("--all-flows", action="store_true")
    e.add_argument("--pdk", choices=PDKS, default=DEFAULT_PDK, help="sky130 (default) or asap7 (the ASAP7 view)")
    e.set_defaults(fn=cmd_export)

    x = sub.add_parser("asap7", parents=[common],
                       help="the ASAP7 view's columns (leaderboard/asap7/<task>.json): check them offline (default), "
                       "re-derive them (--rescore) or measure and write them (--write)")
    x.add_argument("--task")
    g = x.add_mutually_exclusive_group()
    g.add_argument("--rescore", action="store_true",
                   help="also re-weigh every entry (score/ppa.py --pdk asap7; Yosys and the ASAP7 liberty) and "
                   "require the same columns, bit for bit")
    g.add_argument("--write", action="store_true",
                   help="measure every design of the task(s) and write the file(s) (refused when an entry would not "
                   "be bound to its design's sources)")
    x.set_defaults(fn=cmd_asap7)

    u = sub.add_parser("submit", parents=[common],
                       help="hand a record in: open the pull request that adds its three files (with git and gh)")
    u.add_argument("--task", required=True)
    u.add_argument("--record", required=True, metavar="HASH",
                   help="the record's hash, or its first 12 characters or more, as `add` prints them")
    u.add_argument("--repo", metavar="URL",
                   help="the public repository on GitHub (default: site/config.json `repo_url`)")
    u.add_argument("--dry-run", action="store_true",
                   help="print the steps and the pull request's text; change and send nothing")
    u.set_defaults(fn=cmd_submit)
    return ap


def main(argv=None):
    args = make_parser().parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
