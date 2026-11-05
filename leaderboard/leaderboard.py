#!/usr/bin/env python3
"""svGolf leaderboard: records, verification, Pareto frontier and boards.

Records of accepted submissions, their verification, the Pareto frontier of
the ranked score (the sky130 A0' area in um^2 and time in ps: the critical-path
delay, or cycles x the clock period of a clocked task) and the ranked boards.
Area in GE and depth are extra columns.

    leaderboard.py add --task T --player P [--assisted-by X ...] --sv F.sv --lean F.lean
                       [--notes TEXT] [--from-check RESULT.json] [--date YYYY-MM-DD]
                       [--postsynth full|light]
    leaderboard.py verify [--task T] [--offline | --full]
    leaderboard.py pareto --task T [--format text|json] [--unassisted] [--axes A,B,...]
    leaderboard.py board  --task T [--format md|json] [--unassisted] [--all-flows]
    leaderboard.py export --out FILE.md [--all-flows]
    leaderboard.py seed-references [--task T]

One record per ACCEPTED submission, written to
`leaderboard/data/<task>/<record_hash>.json` next to copies of the two
submitted files (`<record_hash>.sv`, `<record_hash>.lean`), so an entry can be
re-verified. The record format, the policies (Pareto frontier, optional depth
budget, staleness) and the verification levels are documented in
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
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
DEFAULT_DATA = os.path.join(HERE, "data")
DEFAULT_TASKS = os.path.join(SVGOLF, "tasks")
CHECK_PY = os.path.join(SVGOLF, "check.py")
SCORE_PY = os.path.join(SVGOLF, "score", "score.py")
PPA_PY = os.path.join(SVGOLF, "score", "ppa.py")
PPA_PINS = os.path.join(SVGOLF, "score", "ppa_pins.json")
PPA_MAPPED_PINS = os.path.join(SVGOLF, "score", "ppa_mapped_pins.json")
PPA_MAPPED_SCRIPT = os.path.join(SVGOLF, "score", "ppa_mapped.ys")

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
# `ppa.mapped` (an unranked research column set beside A0''s, with its own field names, version and hashes; neither flow is
# official). A record without it, every record made before WP-X4, stays valid and verifies as it did.
PPA_MAPPED_KEY = "mapped"
OFFICIAL_PPA_MODE = "require"
# Every check an official artifact comes from runs its untrusted processes in the OS sandbox (WP-S): the
# mechanism missing, or failing its self-test, is an infrastructure error, never a record made without it.
OFFICIAL_SANDBOX_MODE = "require"

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
)
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
    record needs the full check)."""
    if not isinstance(res, dict):
        return ["the check result is not a JSON object"]
    p = []
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
    ps = _get(res, "stages", "postsynth")
    if not (isinstance(ps, dict) and isinstance(ps.get("vectors"), int)
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
            "verilator": ps.get("verilator"),
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
        "postsynth": {"point": ps.get("point"), "vectors": ps["vectors"],
                      "mismatches": ps["mismatches"], "salted": bool(ps.get("salted")),
                      "seed": ps.get("seed"), "mode": record_mode(ps),
                      "full_vectors": ps.get("full_vectors", ps["vectors"])},
        "notes": notes,
    }
    if res.get("ppa") is not None:
        rec[PPA_KEY] = copy.deepcopy(res["ppa"])
    if any(k in sc for k in CLOCKED_SCORE_KEYS):
        # a clocked result's ranked score (check.py `score_clocked`): validate_record holds it to the `ppa` block
        rec["score"].update({k: sc[k] for k in CLOCKED_SCORE_KEYS + ("ffs",) if k in sc})
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
    else:
        p.append("checker must be an object")
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
    need(isinstance(ps, dict) and ps.get("mismatches") == 0 and isinstance(ps.get("vectors"), int),
         "postsynth must record vectors and mismatches 0")
    if isinstance(ps, dict):
        need(record_mode(ps) in POSTSYNTH_MODES, "postsynth.mode must be 'light' or 'full'")
        need(ps.get("full_vectors") is None or (isinstance(ps["full_vectors"], int)
                                                and not isinstance(ps["full_vectors"], bool)
                                                and ps["full_vectors"] >= 0),
             "postsynth.full_vectors must be a non-negative integer")
    if PPA_KEY in rec:
        bad = validate_ppa(rec[PPA_KEY])
        p += bad
        if not bad:
            p += ppa_score_problems(rec)
    if isinstance(s, dict) and any(k in s for k in CLOCKED_SCORE_KEYS):
        p += clocked_score_problems(rec)
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
# ranking: the Pareto frontier, layers, the board (pure)
# ---------------------------------------------------------------------------

# The ranked axes (decided 11/03: sky130 A0' is the ranked metric). Both "lower is better", both exact
# integers: the A0' area in 1e-4 um^2 (`ppa.area_e4um2_sky130`) and the time in ps, which is the
# critical-path delay of a combinational design (`ppa.delay_ps_sky130`) and cycles x the
# register-to-register period of a clocked one (`score.time_ps`, check.py's clocked score). Area in GE
# (`score.area_mge`) and depth (`score.depth`) are extra columns; they rank nothing.
RANKED_AXES = ("area_um2_sky130", "time_ps")


def ranked_columns(rec):
    """{area_e4um2, time_ps, cycles, period_ps} of a record's ranked score, or None if it has no numeric
    `ppa` block (a record made before the columns, or of a design the pinned flow could not weigh).
    `cycles` and `period_ps` are None for a combinational record."""
    b = rec.get(PPA_KEY)
    if not (isinstance(b, dict) and b.get("available") is True):
        return None
    s = rec.get("score") or {}
    if "time_ps" in s:          # a clocked record: cycles x period (validate_record checks it against the block)
        return {"area_e4um2": b.get("area_e4um2_sky130"), "time_ps": s["time_ps"], "cycles": s.get("cycles"),
                "period_ps": s.get("period_ps")}
    return {"area_e4um2": b.get("area_e4um2_sky130"), "time_ps": b.get("delay_ps_sky130"), "cycles": None,
            "period_ps": None}


def row_of(rec):
    """The flat row the ranking works on: the ranked pair (`area_e4um2`, `time_ps`; None without sky130
    columns) and the extra columns (`area_mge`, `depth`, ...)."""
    cols = ranked_columns(rec) or {"area_e4um2": None, "time_ps": None, "cycles": None, "period_ps": None}
    return {"record_hash": rec["record_hash"], "task": rec["task"], "player": rec["player"],
            "assisted_by": list(rec["assisted_by"]), **cols, "area_mge": rec["score"]["area_mge"],
            "depth": rec["score"]["depth"], "proof_lines": rec["proof"]["lines"],
            "submitted_at": rec["submitted_at"], "postsynth": record_mode(rec["postsynth"])}


def has_ranked_columns(r):
    """A row carries both ranked numbers (a record without sky130 columns does not: it is not ranked)."""
    return all(isinstance(r.get(k), int) and not isinstance(r.get(k), bool) for k in ("area_e4um2", "time_ps"))


def row_key(r):
    """The total order every listing uses: sky130 area, then time, then the earlier
    date first (on a tie in both the earlier record stands), then player, then
    record hash (so equal scores are ordered the same way on every machine). A row
    without the sky130 columns sorts after every row with them, by area in GE then
    depth."""
    if not has_ranked_columns(r):
        return (1, r["area_mge"], r["depth"], r["submitted_at"], r["player"], r["record_hash"])
    return (0, r["area_e4um2"], r["time_ps"], r["submitted_at"], r["player"], r["record_hash"])


def dominates(a, b):
    """`a` beats `b`: no worse on both ranked axes (sky130 area, time) and strictly
    better on one. Equal scores do not dominate each other (ties are kept)."""
    return (a["area_e4um2"] <= b["area_e4um2"] and a["time_ps"] <= b["time_ps"]
            and (a["area_e4um2"] < b["area_e4um2"] or a["time_ps"] < b["time_ps"]))


def pareto_layers(rows):
    """Non-dominated sorting: layer 1 is the Pareto frontier, layer 2 the
    frontier of the rest, and so on. Each layer is in `row_key` order. Every
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
    c = rec["checker"]
    return {"yosys": c.get("yosys"), "canon_script_sha256": c.get("canon_script_sha256"),
            "script_sha256": c.get("script_sha256"), "ge_table_sha256": c.get("ge_table_sha256")}


def flow_mismatch(rec_flow, flow):
    """The keys in which a record's flow differs from `flow` (the current one);
    keys `flow` leaves None are not compared."""
    return sorted(k for k, v in flow.items() if v is not None and rec_flow.get(k) != v)


def _competition_ranks(rows):
    """Rank by (sky130 area, time) with ties sharing a rank (1, 1, 3, ...)."""
    ranks, prev, rank = [], None, 0
    for i, r in enumerate(rows):
        k = (r["area_e4um2"], r["time_ps"])
        if k != prev:
            rank, prev = i + 1, k
        ranks.append(rank)
    return ranks


def unranked_reason(rec, task, *, flow=None, identity=None, input_drive=None):
    """Why `rec` is not ranked on `task`'s board, or None if it is. Pure. In order: scored at another
    point; checked under another flow (`flow` given); no sky130 columns (a record made before them: not
    ranked until it is backfilled, i.e. checked again) or columns that were not computed; columns of
    another `ppa_version`/liberty/pins than `identity` (given); weighed under another input drive than
    the task's `input_drive` (given)."""
    point = scoring_point(task)
    if rec["score"]["scoring_point"] != point:
        return f"scored at {rec['score']['scoring_point']}, not at {point}"
    if flow is not None and flow_mismatch(flow_of(rec), flow):
        return "checked under another flow (" + ", ".join(flow_mismatch(flow_of(rec), flow)) + " differ)"
    b = rec.get(PPA_KEY)
    if b is None:
        return ("no sky130 columns (a record made before them): not ranked until it is backfilled "
                "(checked again, which records them)")
    if not (isinstance(b, dict) and b.get("available") is True):
        return "the sky130 columns were not computed: " + str((b or {}).get("reason", "?"))[:120]
    if not has_ranked_columns(row_of(rec)):
        return "the sky130 columns lack a ranked number"
    if identity is not None and any(b.get(k) != identity.get(k) for k in PPA_IDENTITY):
        return ("sky130 columns computed under another version ("
                + ", ".join(k for k in PPA_IDENTITY if b.get(k) != identity.get(k)) + " differ)")
    return ppa_drive_mismatch(b, input_drive)


def build_board(task, records, *, flow=None, unassisted=False, identity=None, input_drive=None):
    """The board of one task, ranked on the sky130 A0' area and time (RANKED_AXES). `records` are
    its records (others are ignored); `flow`, if given, is the current pinned flow {yosys,
    canon_script_sha256, script_sha256, ge_table_sha256}; `identity` (`ppa_identity()`) and
    `input_drive` (`ppa_setup_now(task)["input_drive"]`), if given, are what the sky130 columns must
    have been computed under. A record that is not comparable (`unranked_reason`: another point, flow,
    PPA identity or input drive, or no sky130 columns) is listed as `unranked` with the reason instead
    of ranked. With `unassisted`, only records with an empty `assisted_by` are considered."""
    point = scoring_point(task)
    budget = effective_depth_budget(task)
    ranked, unranked = [], []
    for rec in sorted((r for r in records if r["task"] == task["name"]),
                      key=lambda r: row_key(row_of(r))):
        if unassisted and rec["assisted_by"]:
            continue
        row = row_of(rec)
        why = unranked_reason(rec, task, flow=flow, identity=identity, input_drive=input_drive)
        if why:
            unranked.append(dict(row, reason=why))
        else:
            ranked.append(row)
    layers = pareto_layers(ranked)
    for r in ranked:
        r["over_budget"] = budget is not None and r["depth"] > budget
    frontier = layers[0] if layers else []
    dominated = [dict(r, layer=k + 2) for k, layer in enumerate(layers[1:]) for r in layer]
    board = {"task": task["name"], "title": task.get("title", ""), "scoring_point": point,
             "ranked_axes": list(RANKED_AXES), "depth_budget": budget, "flow_checked": flow is not None,
             "ppa_identity": identity, "input_drive": input_drive,
             "frontier": [dict(r, layer=1) for r in frontier], "dominated": dominated,
             "budget_ranking": None, "unranked": unranked,
             "unassisted_only": bool(unassisted)}
    if budget is not None:
        within = sorted((r for r in ranked if not r["over_budget"]), key=row_key)
        over = sorted((r for r in ranked if r["over_budget"]), key=row_key)
        board["budget_ranking"] = (
            [dict(r, rank=k) for r, k in zip(within, _competition_ranks(within))]
            + [dict(r, rank=None) for r in over])
    return board


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
              "of the vectors, local feedback); the others with the full check.")


def _record_cell(row):
    """The record column: the hash prefix, and `light` after it for a record
    whose post-synthesis check ran in light mode."""
    return f"`{row['record_hash'][:12]}`" + (" light" if row.get("postsynth") == "light" else "")


def _has_light(board):
    rows = (board["frontier"] + board["dominated"] + (board["budget_ranking"] or [])
            + board["unranked"])
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


def fmt_time(r):
    """A row's ranked time as text: the delay in ps ('2611'), or for a clocked record the time and how it is
    made ('42784 (4 x 10696)'); '-' without sky130 columns."""
    if r.get("time_ps") is None:
        return "-"
    if r.get("cycles") is not None:
        return f"{r['time_ps']} ({r['cycles']} x {r['period_ps']})"
    return str(r["time_ps"])


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
    n = len(board["frontier"]) + len(board["dominated"])
    if n == 0:
        lines += ["No ranked records.", ""]
    else:
        header = ["#", "layer", "player", "assisted by", "area (um^2)", "time (ps)", "area (GE)", "depth",
                  "proof lines", "date", "record"]
        aligns = ["r", "r", "l", "l", "r", "r", "r", "r", "r", "l", "l"]
        if budget is not None:
            header.insert(8, "budget")
            aligns.insert(8, "l")
        trs = []
        for i, r in enumerate(board["frontier"] + board["dominated"], 1):
            cells = [str(i), str(r["layer"]), md_escape(r["player"]), _assist_cell(r),
                     fmt_um2(r["area_e4um2"]), fmt_time(r), fmt_ge(r["area_mge"]), str(r["depth"]),
                     str(r["proof_lines"]), r["submitted_at"], _record_cell(r)]
            if budget is not None:
                cells.insert(8, "over" if r["over_budget"] else "ok")
            trs.append(cells)
        lines += [f"{h}# Pareto frontier first (layer 1), then dominated entries by layer", ""]
        lines += _md_table(header, aligns, trs) + [""]
    if board["budget_ranking"] is not None:
        lines += [f"{h}# Best area under the depth budget (depth <= {budget})", ""]
        trs = [[("-" if r["rank"] is None else str(r["rank"])), md_escape(r["player"]),
                _assist_cell(r), fmt_um2(r["area_e4um2"]), fmt_time(r), fmt_ge(r["area_mge"]),
                str(r["depth"]), "over budget" if r["rank"] is None else "ok", r["submitted_at"],
                _record_cell(r)] for r in board["budget_ranking"]]
        lines += _md_table(["rank", "player", "assisted by", "area (um^2)", "time (ps)", "area (GE)", "depth",
                            "budget", "date", "record"], ["r", "l", "l", "r", "r", "r", "r", "l", "l", "l"], trs)
        lines.append("")
    if board["unranked"]:
        lines += [f"{h}# Not ranked", ""]
        trs = [[md_escape(r["player"]), fmt_um2(r["area_e4um2"]), fmt_time(r), fmt_ge(r["area_mge"]),
                str(r["depth"]), _record_cell(r), md_escape(r["reason"])] for r in board["unranked"]]
        lines += _md_table(["player", "area (um^2)", "time (ps)", "area (GE)", "depth", "record", "why"],
                           ["l", "r", "r", "r", "r", "l", "l"], trs) + [""]
    if _has_light(board):
        lines += [LIGHT_NOTE, ""]
    return "\n".join(lines)


def render_export(boards):
    """All tasks' boards as one Markdown document."""
    parts = ["# svGolf leaderboard", "",
             "Generated by `leaderboard/leaderboard.py export` from the records under "
             "`leaderboard/data/`. Ranked on sky130 A0' (`score/ppa.py`): the area in um^2 and the "
             "time in ps (the critical-path delay; on a clocked task, cycles x the clock period). Lower "
             "is better on both; layer 1 is their Pareto frontier. Area in GE and depth are extra "
             "columns. A record without sky130 columns is not ranked until it is backfilled.", ""]
    parts += [render_markdown(b, 2) for b in boards]
    return "\n".join(parts).rstrip("\n") + "\n"


def render_pareto_text(board):
    lines = []
    point = ", ".join(f"{k}={v}" for k, v in board["scoring_point"].items()) or "fixed size"
    lines.append(f"{board['task']}: Pareto frontier of (sky130 area, time) at {point} "
                 f"({len(board['frontier'])} of {len(board['frontier']) + len(board['dominated'])}"
                 " ranked records)")
    if not board["frontier"]:
        lines.append("  (no ranked records)")
    else:
        rows = [(fmt_um2(r["area_e4um2"]), fmt_time(r), fmt_ge(r["area_mge"]), str(r["depth"]), r)
                for r in board["frontier"]]
        w = [max(len(head), *(len(x[k]) for x in rows))
             for k, head in enumerate(("area um^2", "time ps", "area GE", "depth"))]
        lines.append("  " + " ".join(f"{head:>{n}}" for head, n in zip(("area um^2", "time ps", "area GE", "depth"), w))
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
# The default board is RANKED_AXES (sky130 A0' area, time) and nothing here changes it: `pareto`
# without `--axes` prints the default. With `--axes` the frontier is taken over the named axes only,
# for the records that carry all of them (`--axes area_um2_sky130,time_ps` is the default board's
# frontier). Every axis is "lower is better" and an exact integer (areas in um^2 are compared as
# integers in 1e-4 um^2, the unit the columns are exact in); a record is on the frontier iff no other
# record is at least as good on every axis and strictly better on one (ties are kept, as on the
# default board).

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


def build_axes_view(task, records, axes, *, flow=None, identity=None, mapped_identity=None, unassisted=False,
                    input_drive=None):
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
             f"({len(view['frontier'])} of {n} records that carry the axes)"]
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
                  recheck=None, ppa_identity=None, ppa_setup=None):
    """Verify one stored record at `path` (a `.json` next to its two files).

    Always: the record is well-formed, its `record_hash` is the hash of its
    canonical JSON and the file's name, the two stored files exist and have the
    recorded sha256, the score arithmetic is consistent (area = sum of the gate
    weights of `score/ge.json` when that table is the recorded one), the axioms
    are within the task's allowed set.

    `rescore(sv_path)` (optional): returns score.py's result for the stored
    design; the score, gate mix, canonical text hash and canonical RTLIL hash
    must equal the record's (skipped, with a note, if the flow has changed).
    `recheck(sv_path, lean_path)` (optional): returns check.py's full result;
    it must accept, with the same canonical hash, axioms and (same flow) score.

    A record checked under another flow than the current `flow` is `stale`
    (not a failure): its score can no longer be reproduced or compared.

    `ppa_identity` (`ppa_identity()`) and `ppa_setup` (`ppa_setup_now(task)`, optional): a record
    whose sky130 columns are of the current identity must name the timing setup the task's
    configuration gives now. Its `setup.input_drive` another than the task's (`task.json`
    `input_drive`, a task field outside the pins file): `stale`, the columns are not compared
    (rescore, recheck) and the views do not rank them. Its `pi_slew_ps` / `po_load_ff` other than
    the pins file it names: FAIL (that file cannot have given them). A rescore or recheck compares
    the whole `setup` with the fresh weighing's (PPA_COMPARED)."""
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
    ge_path = os.path.join(SVGOLF, "score", "ge.json")
    if os.path.isfile(ge_path) and sha256_file(ge_path) == ck["ge_table_sha256"]:
        with open(ge_path, encoding="utf-8") as fh:
            ge = {k: round(v * 1000) for k, v in json.load(fh).items() if not k.startswith("_")}
        unknown = sorted(set(sc["gates"]) - set(ge))
        if unknown:
            res.fails.append(f"gate types the GE table does not price: {unknown}")
        elif sum(ge[g] * n for g, n in sc["gates"].items()) != sc["area_mge"]:
            res.fails.append("score.area_mge is not the sum of the gate weights in score/ge.json")
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
    if flow is not None:
        diff = flow_mismatch(flow_of(rec), flow)
        if diff:
            same_flow = False
            res.stale.append("checked under another flow (" + ", ".join(diff)
                             + " differ): the score is no longer reproducible or comparable")
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
    return res


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


def checker_file_hashes(svgolf=SVGOLF):
    out = {}
    for rel in CHECKER_FILES:
        p = os.path.join(svgolf, rel)
        if os.path.isfile(p):
            out[rel] = sha256_file(p)
    return out


def collect_environment(svgolf=SVGOLF):
    tc = os.path.join(svgolf, "lean-toolchain")
    toolchain = None
    if os.path.isfile(tc):
        with open(tc, encoding="utf-8") as fh:
            toolchain = fh.read().strip() or None
    return {"svgolf_revision": git_revision(svgolf), "lean_toolchain": toolchain,
            "files": checker_file_hashes(svgolf)}


def current_flow(svgolf=SVGOLF):
    """The pinned flow as it is now: the sha256 of the two scripts and the GE
    table, and Yosys's version line (None if Yosys cannot be run)."""
    sc = os.path.join(svgolf, "score")
    yosys = os.environ.get("SVGOLF_YOSYS") or "yosys"
    try:
        ver = subprocess.run([yosys, "-V"], capture_output=True, text=True,
                             check=True).stdout.strip() or None
    except (OSError, subprocess.CalledProcessError):
        ver = None

    def sha(name):
        p = os.path.join(sc, name)
        return sha256_file(p) if os.path.isfile(p) else None

    return {"yosys": ver, "canon_script_sha256": sha("canon.ys"),
            "script_sha256": sha("svgolf.ys"), "ge_table_sha256": sha("ge.json")}


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


def run_rescore(sv, task_dir, *, score_py=SCORE_PY, timeout=3600, ppa_py=None, mapped=True):
    """score.py on the stored design at the task's scoring point. With `ppa_py` (score/ppa.py,
    for a record that carries PPA columns) the same pinned flow runs ONCE through ppa.py, whose
    `score` is score.py's result unchanged, and the result carries the weighed columns as
    `ppa`; if ppa.py cannot weigh (the pinned liberty is absent here, say), score.py runs
    alone and `ppa` is `{"available": false, "reason": ...}`: the rescore itself never
    depends on the liberty. `mapped` False passes `--no-mapped` (no flow A1' mapping, for a
    record that has no mapped columns to reproduce)."""
    if ppa_py:
        proc = subprocess.run([checker_python(), ppa_py, sv, "--task", task_dir] + ([] if mapped else ["--no-mapped"]),
                              capture_output=True, text=True, timeout=timeout)
        try:
            out = json.loads(proc.stdout)
        except ValueError:
            out = {}
        if proc.returncode == 0 and "score" in out and "ppa" in out:
            return dict(out["score"], ppa=dict(out["ppa"], available=True))
        why = " ".join(str(out.get("error", proc.stderr[-300:] or proc.returncode)).split())
        return dict(run_rescore(sv, task_dir, score_py=score_py, timeout=timeout),
                    ppa={"available": False, "reason": why[:400]})
    proc = subprocess.run([checker_python(), score_py, sv, "--task", task_dir],
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

def load_task(tasks_dir, name):
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


def add_submission(args, *, sv, lean, player, assisted_by, notes, date, from_check=None):
    """Check (or read the result of) one submission and record it. Returns the
    record's path. Raises Refused (not accepted / malformed / duplicate) or
    RuntimeError (infrastructure)."""
    task = load_task(args.tasks_dir, args.task)
    mode = getattr(args, "postsynth", None) or DEFAULT_POSTSYNTH_MODE
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
    if problems:
        raise Refused(problems)
    for _, other, _ in load_records(args.data_dir, args.task):
        if (isinstance(other, dict) and other.get("player") == player
                and _get(other, "files", "sv", "sha256") == sha256_bytes(sv_bytes)
                and _get(other, "files", "lean", "sha256") == sha256_bytes(lean_bytes)):
            raise Refused([f"already recorded: {other.get('record_hash')} (same player, same "
                           "files)"])
    env_before = collect_environment()    # read BEFORE the check: the checker as it ran
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
        changed = sorted(k for k, v in collect_environment()["files"].items()
                         if env_before["files"].get(k) != v)
        if changed:
            raise Refused([f"checker files changed while the check ran ({', '.join(changed)}): "
                           "the result cannot be attributed to one checker; run it again"])
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
    if record_mode(ps) == "light":
        print(f"  NOTE: the post-synthesis check ran in LIGHT mode ({ps['vectors']} of "
              f"{ps.get('full_vectors', ps['vectors'])} vectors): this is a light record, marked "
              "so on the board, for local use; an official record needs `add` without "
              "`--postsynth light` (the full check)")
    else:
        print(f"  post-synthesis check: full mode ({ps['vectors']} vectors)")
    pb = rec.get(PPA_KEY)
    if isinstance(pb, dict) and pb.get("available") is True:
        cols = ranked_columns(rec)
        print(f"  the ranked sky130 score (A0', {pb['ppa_version']}): {pb['area_um2_sky130']} um^2, "
              f"{fmt_time(cols)} ps; input drive {ppa_input_drive(pb) or '(none named)'}")
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
                path = add_submission(args, sv=sv, lean=lean, player="svgolf-reference",
                                      assisted_by=["Claude (Anthropic)"],
                                      notes="reference solution", date=args.date or today_utc())
                print(f"seeded {name}: {ref['sv']} -> {os.path.relpath(path)}")
            except Refused as e:
                print(f"{name}: {ref['sv']}: not added: " + "; ".join(e.problems))
                if not any(p.startswith("already recorded") for p in e.problems):
                    status = 1
            except (RuntimeError, OSError, ValueError) as e:
                print(f"{name}: {ref['sv']}: error: {e}", file=sys.stderr)
                return 2
    return status


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
    flow = current_flow()
    files = checker_file_hashes()
    identity = ppa_identity()
    failed = stale = 0
    for path, rec, err in loaded:
        label = os.path.relpath(path, args.data_dir)
        if not isinstance(rec, dict):
            print(f"[FAIL] {label}: not a JSON object" + (f": {err}" if err else ""))
            failed += 1
            continue
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
        rescore = (None if args.offline or args.full or task is None
                   else (lambda sv, td=task_dir, w=has_ppa, m=has_mapped: run_rescore(
                       sv, td, score_py=args.score_py, ppa_py=args.ppa_py if w else None, mapped=m)))
        # a record WITH columns is rechecked under `--ppa require` (the official mode: the columns must
        # reproduce); a record made before them is rechecked as it always was, without needing the liberty
        recheck = (None if not args.full or task is None else
                   (lambda sv, lean, td=task_dir, w=has_ppa: run_check(
                       td, sv, lean, check_py=args.check_py, lean_wrap=args.lean_wrap,
                       postsynth="full", ppa=OFFICIAL_PPA_MODE if w else "off", sandbox=args.sandbox)[1]))
        r = verify_record(path, rec, task, flow=flow, current_files=files, rescore=rescore,
                          recheck=recheck, ppa_identity=identity,
                          ppa_setup=ppa_setup_now(task) if task is not None else None)
        who = f"{rec.get('player')} {score_text(rec)}" if not validate_record(rec) else "malformed"
        detail = "; ".join(r.fails + r.stale + r.notes)
        task_name, _, stem = label[:-len(".json")].partition(os.sep)
        print(f"[{r.status}] {task_name}/{stem[:12]}: {who}: {detail or 'hashes and arithmetic ok'}")
        failed += bool(r.fails)
        stale += bool(r.stale) and not r.fails
    level = "offline" if args.offline else ("full re-check" if args.full else "hashes + rescore")
    print(f"verify ({level}): {len(loaded)} records, {failed} failed, {stale} stale")
    return 1 if failed else 0


def _boards(args, names, unassisted=False):
    """The boards of `names`, ranked under the current flow and sky130 identity and each task's input drive
    (`--all-flows`: none of them checked; a record without sky130 columns is never ranked)."""
    flow = None if args.all_flows else current_flow()
    identity = None if args.all_flows else ppa_identity()
    records = good_records(load_records(args.data_dir), warn=lambda m: print(m, file=sys.stderr))
    out = []
    for n in names:
        task = load_task(args.tasks_dir, n)
        out.append(build_board(task, [r for r in records if r["task"] == n], flow=flow, unassisted=unassisted,
                               identity=identity,
                               input_drive=None if args.all_flows else ppa_setup_now(task).get("input_drive")))
    return out


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
    view = build_axes_view(task, records, axes, flow=None if args.all_flows else current_flow(),
                           identity=None if args.all_flows else ppa_identity(),
                           mapped_identity=None if args.all_flows else ppa_mapped_identity(),
                           unassisted=args.unassisted,
                           input_drive=None if args.all_flows else ppa_setup_now(task).get("input_drive"))
    print(json.dumps(view, indent=2, sort_keys=True) if args.format == "json"
          else render_axes_text(view))
    return 0


def cmd_pareto(args):
    if getattr(args, "axes", None):
        return cmd_pareto_axes(args)
    try:
        (board,) = _boards(args, [args.task], args.unassisted)
    except (FileNotFoundError, ValueError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    if args.format == "json":
        print(json.dumps({"task": board["task"], "frontier": board["frontier"]}, indent=2,
                         sort_keys=True))
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
        fh.write(render_export(boards))
    print(f"wrote {args.out}: {len(boards)} tasks, "
          f"{sum(len(b['frontier']) + len(b['dominated']) for b in boards)} ranked records")
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
    common.add_argument("--sandbox", choices=("off", "auto", "require"), default=OFFICIAL_SANDBOX_MODE,
                        help="check.py's --sandbox for the checks `add` and `verify --full` run (default "
                        "`require`: an official record is made with the OS sandbox or not at all)")
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
                   help="use this check.py result instead of running check.py")
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

    for name, fn, h in (("pareto", cmd_pareto, "the (sky130 area, time) Pareto frontier of a task"),
                        ("board", cmd_board, "the ranked board of a task")):
        b = sub.add_parser(name, parents=[common], help=h)
        b.add_argument("--task", required=True)
        b.add_argument("--format", choices=("md", "json") if name == "board" else ("text", "json"),
                       default="md" if name == "board" else "text")
        b.add_argument("--unassisted", action="store_true",
                       help="only records with an empty assisted_by")
        b.add_argument("--all-flows", action="store_true",
                       help="rank records checked under another flow too")
        if name == "pareto":
            b.add_argument("--axes", metavar="A,B,...",
                           help="opt-in: the n-dimensional Pareto frontier over these axes, for the "
                           "records that carry them (known: " + ", ".join(AXES) + "), e.g. "
                           "--axes area_mge,depth (the GE columns). Without --axes: the ranked board, "
                           "(area_um2_sky130, time_ps)")
        b.set_defaults(fn=fn)

    e = sub.add_parser("export", parents=[common], help="all tasks' boards as one Markdown file")
    e.add_argument("--out", required=True)
    e.add_argument("--all-flows", action="store_true")
    e.set_defaults(fn=cmd_export)
    return ap


def main(argv=None):
    args = make_parser().parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
