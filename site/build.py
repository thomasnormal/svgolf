#!/usr/bin/env python3
"""svGolf's static site generator.

    python3.12 site/build.py [--out DIR] [--offline] [--strict] [--revision REV] [--denylist FILE]

Run from svgolf/ (any directory works; paths are taken from this file). Any
Python 3.9 or later, standard library only. It writes the whole site to
`site/_out/` (git-ignored) or to `--out`:

  index.html                      what svGolf is, a card per task (par, record), the loop
  tasks/<t>/index.html            a listed task: par, record and how far under par on the score
                                  (area x time on sky130: leaderboard/combined.py); the score card
                                  (the score of each entry over time); the task (statement,
                                  interface, the trusted statement as a panel of property cards and
                                  the definitions they use (props.py), with Spec.lean and its trusted
                                  import closure, how to participate, how to submit) beside the
                                  leaderboard (by score); the designs compared (any two numbers
                                  against each other, with the Pareto front, at the scored point or,
                                  measured, not ranked, at any other point of score/points.json; and
                                  how the designs scale: one number against the task's parameter, a
                                  line per design); the proved references
                                  (par), the baselines, what does not count; the files it offers
                                  (Spec.lean, Properties.lean, reference/, baselines/) next to it,
                                  byte-identical
  tasks/<t>/properties.html       the task's Properties.lean verbatim, an anchor per line and per
                                  declaration (where a property card's "Open in code" lands)
  tasks/<t>/records/<hash>.html   one page per record, with its .json, .sv and .lean (byte-identical)
  trusted/<module>.html           every module of the statements' trusted import closure, verbatim,
                                  an anchor per line and per declaration (leansrc.py)
  rules.html refusals.html proving.html roadmap.html about.html
  reproduce.html                  score/PPA.md's "Reproduce a score": the pinned tools, files and commands
  llms.txt data/site.json data/tasks/<t>.json style.css site.js charts.js

The look is style.css's design system and page.py's components; every page reads without
JavaScript (site.js adds the copy buttons of code blocks and the property panel's tabs). A task
page's charts are drawn here as SVG (svgplot.py; the numbers come from metrics.py) and its data
is embedded as inert JSON; charts.js adds the score chart's linear/log switch, tooltips, the
explorer's point selector and axis menus, and the scaling view's metric menu and switches.

Inputs, all from the repository: tasks/<t>/ (task.json, README.md, Spec.lean,
reference/, and properties.json + Properties.lean: the statement as named
properties, the Lean text of each cut from its file by declaration name),
tests/expected.json (scores, baselines, attacks, negatives and the
pinned flow), score/measured/<t>.json (the designs measured at every
point of score/points.json by score/points.py), the records under leaderboard/data/ (read and ranked by
leaderboard.py's own pure functions), README.md, PROVING.md, the refusal
register docs/sv-refusals.json of lean-surfaces, and site/config.json +
site/content/. Nothing is deployed, pushed or uploaded: the output is a
directory. Preview: `python3 -m http.server -d site/_out -b 127.0.0.1`.

The public texts of a task are curated, never copied from the internal notes:
`content/tasks/<t>.md` (the statement), `content/tasks/<t>.json` (the display
title and subtitle, one sentence per reference and baseline, an optional
banlist note) and `content/attacks/<t>.json` (one sentence per rejected
negative or attack). The `why` and `note` strings of tests/expected.json and
task.json are internal and are not rendered; a rejected design is shown with its
comments left out (they are development notes). The records of
`config.json`'s `reference_player` are par, the bar to beat: they are shown with
the proved references, never ranked among the players.

How to submit: until `config.json` names the public repository (`repo_url`),
a task page says that public submissions open when it is published and shows
the local flow only; with a `repo_url`, it shows the clone and the pull request.

Boards are built under the flow pinned in tests/expected.json, so the output
is a function of the repository alone. Unless `--offline`, the build first
checks that the machine's flow (leaderboard.py's `current_flow()`: the Yosys
version and the hashes of the two scripts and the GE table) matches that pin
on every key; a missing Yosys counts as a mismatch. Deterministic: no clock is
read, iteration is sorted, areas stay integer milli-GE until printed, and
chart coordinates are rounded to 0.1, so two builds are byte-identical.

Guards, each fatal: every relative link and anchor of the output resolves;
no `config.json` denylist entry occurs in it (a plain string anywhere, an
internal marker in the site's own text: see `check_denylist`); a stale
redaction (its text no longer in the source) fails; an unsupported Markdown
construct fails with file:line. `--denylist FILE` adds entries (a JSON list in config.json's format)
kept outside the repository. `--strict` makes the warnings fatal too (today:
a task with no `content/tasks/<t>.md`, whose README intro is used instead, a
task that `config.json` does not list, and a missing or stale curated text in
`content/tasks/<t>.json` or `content/attacks/<t>.json`).

Exit status: 0 built, 1 a guard or check failed, 2 usage error.
"""

import argparse
import difflib
import hashlib
import html.parser
import importlib.util
import json
import os
import posixpath
import re
import shutil
import sys

sys.dont_write_bytecode = True
SITE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(SITE)
sys.path.insert(0, SITE)


def _load_layout():
    """check/layout.py (where lean-surfaces is, in either layout), loaded by path."""
    spec = importlib.util.spec_from_file_location("svgolf_layout", os.path.join(SVGOLF, "check", "layout.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


layout = _load_layout()
LAYOUT = layout.LAYOUT                            # "inside" lean-surfaces, or "standalone"
LS_ROOT = layout.LS_ROOT                          # lean-surfaces: docs/, LeanModels/

import leansrc                                    # noqa: E402  (the site's own modules)
import md                                         # noqa: E402
import metrics                                    # noqa: E402
import page                                       # noqa: E402
import props                                      # noqa: E402
import svgplot                                    # noqa: E402
from metrics import combined                      # noqa: E402  (leaderboard/combined.py: the score)
from highlight import highlight, language_of, tokens   # noqa: E402
from page import esc, code                        # noqa: E402

OUT_DEFAULT = os.path.join(SITE, "_out")
CONTENT = "svgolf/site/content"                   # the site's own texts (a repository path: `repo_file`)
MARKER = ".svgolf-site"                           # marks a directory this script may replace
SCHEMA = "svgolf-site/1"
TOOLCHAIN_ROOTS = ("Init", "Std", "Lean", "Lake")
KIND_SHORT = {"comb-family": "parametric", "comb-fixed": "fixed size"}
# "What does not count", grouped by where the checker stops (the stages of the refusal register):
# a stage before `solution` refuses the design before any proof is tried, the proof stages reject
# the proof that comes with it, and the stages after them reject the scored netlist.
PROOF_STAGES = ("solution", "integrity", "comparator", "leanchecker")
REJECT_GROUPS = (
    ("before-proof", "Refused before any proof is tried",
     "The checker's static stages read the text itself and refuse it: an operator the task bans, a "
     "construct that two tools read differently, an unknown (<code>x</code> or <code>z</code>) value "
     "that could arise, or a program the language forbids."),
    ("at-proof", "Rejected at the proof",
     "These pass every static check. The proof that comes with each one does not compile, or does "
     "not prove the statement: a design that is wrong somewhere in the task's range (or has other "
     "ports) has no proof at all, and a proof that leaves a goal unproved is never accepted."),
    ("after-proof", "Rejected after scoring",
     "These get through the proof stages and are rejected by scoring or by the post-synthesis check."),
)


def load_leaderboard():
    """leaderboard/leaderboard.py as a module (it is a script, not a package)."""
    path = os.path.join(SVGOLF, "leaderboard", "leaderboard.py")
    spec = importlib.util.spec_from_file_location("svgolf_leaderboard", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


lb = load_leaderboard()


class BuildError(Exception):
    pass


# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------

def repo_file(rel):
    """The file of a repository path. Repository paths are written as in the layout inside
    lean-surfaces, in both layouts: `svgolf/...` is svGolf's own tree, anything else
    (`docs/sv-refusals.json`, `LeanModels/...`) is lean-surfaces' (the parent directory inside
    it, the Lake dependency standalone: check/layout.py)."""
    if rel == "svgolf" or rel.startswith("svgolf/"):
        return os.path.join(SVGOLF, *rel.split("/")[1:])
    return os.path.join(LS_ROOT, rel)


def read_bytes(rel):
    """A repository file (a repository path: `repo_file`)."""
    with open(repo_file(rel), "rb") as fh:
        return fh.read()


def read_text(rel):
    return read_bytes(rel).decode("utf-8")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def rel_link(here, target):
    """`target` (a site path, maybe with #fragment) relative to the page `here`."""
    path, hash_, frag = target.partition("#")
    if not path:
        return "#" + frag
    out = posixpath.relpath(path, posixpath.dirname(here) or ".")
    return out + (hash_ + frag if frag else "")


def root_of(here):
    """The relative prefix from page `here` to the site root."""
    depth = here.count("/")
    return "../" * depth


def ge(mge):
    return f"{lb.fmt_ge(mge)} GE"


def vs_par(area_mge, par_mge):
    """The change of an area against par, as text: '-12.3%', '+0.4%', '±0.0%'."""
    if area_mge is None or not par_mge:
        return "–"
    if area_mge == par_mge:
        return "±0.0%"
    return f"{(area_mge - par_mge) * 100 / par_mge:+.1f}%".replace("-", "−")


def point_key(point):
    """The scoring point as tests/expected.json writes it: 'N=16', 'W=5,P=11', 'default'."""
    return ",".join(f"{k}={v}" for k, v in point.items()) or "default"


def point_text(point):
    return ", ".join(f"{k} = {v}" for k, v in point.items()) or "the one fixed size"


def md_inline(text, resolve=None):
    return md.render_inline(text, resolve_link=resolve or (lambda t: t if re.match(r"^[a-z]+:", t) else None))


def json_text(obj):
    return json.dumps(obj, indent=1, sort_keys=True, ensure_ascii=False) + "\n"


def without_comment_keys(obj):
    """A JSON value without the `_comment`-style keys (any key starting with `_`) of its objects:
    they are notes for the maintainers, not data."""
    if isinstance(obj, dict):
        return {k: without_comment_keys(v) for k, v in obj.items() if not k.startswith("_")}
    if isinstance(obj, list):
        return [without_comment_keys(v) for v in obj]
    return obj


def strip_sv_comments(text):
    """A SystemVerilog design without its comments (the highlighter's tokens decide what is one): a
    line that held only a comment goes, a trailing comment goes with the spaces before it, runs of
    blank lines shrink to one. The code is unchanged (the checker strips the comments too)."""
    out = "".join("\0" if kind == "com" else s for kind, s in tokens(text, "sv"))
    lines = []
    for ln in out.split("\n"):
        if "\0" in ln:
            ln = ln.replace("\0", "").rstrip()
            if not ln.strip():
                continue
        if not ln.strip() and (not lines or not lines[-1].strip()):
            continue
        lines.append(ln)
    while lines and not lines[-1].strip():
        lines.pop()
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# the build context: output files, warnings, links into the repository
# ---------------------------------------------------------------------------

class Site:
    def __init__(self, config, *, strict=False, revision=None):
        self.config = config
        self.strict = strict
        self.revision = revision
        self.files = {}                           # output path -> bytes
        self.copies = set()                       # output paths that are a repository file, byte for byte
        self.player_text = set()                  # what players wrote in records (player, assisted_by, notes)
        self.warnings = []
        self.unlinked = set()                     # repository paths shown as text (no public URL yet)
        self.task_pages = {}                      # repository path -> site path (filled by collect)
        self.flow = None                          # the pinned flow the boards are built under
        self.ppa_identity = None                  # the sky130 identity they are built under (lb.ppa_identity)
        self.stages = []                          # the checker's stages, in order (the refusal register)
        self._sky = None

    def warn(self, msg):
        self.warnings.append(msg)

    def sky130(self):
        """The sky130 and energy goldens (metrics.Sky130), read once."""
        if self._sky is None:
            self._sky = metrics.Sky130(SVGOLF, warn=self.warn)
        return self._sky

    def add(self, path, data):
        if path in self.files:
            raise BuildError(f"two outputs at {path}")
        self.files[path] = data.encode("utf-8") if isinstance(data, str) else data

    def copy(self, path, repo_rel):
        """Offer the repository file `repo_rel` at `path`, byte for byte."""
        self.add(path, read_bytes(repo_rel))
        self.copies.add(path)

    def content(self, rel):
        """A JSON file of site/content/ (`rel` relative to it), or None if there is none."""
        path = f"{CONTENT}/{rel}"
        if not os.path.isfile(repo_file(path)):
            return None
        try:
            return json.loads(read_text(path))
        except ValueError as e:
            raise BuildError(f"{path}: not JSON: {e}")

    def page(self, path, title, body_html, *, active=None, description="", scripts=()):
        self.add(path, page.layout(title=title, body_html=body_html, root=root_of(path), active=active,
                                   description=description, revision=self.revision,
                                   site_name=self.config["site_name"], scripts=scripts))

    # -- links from documents --------------------------------------------

    def site_path_of(self, repo_path):
        """Where the site shows a repository file, or None."""
        mapped = self.config["link_map"]
        if repo_path in mapped:
            return mapped[repo_path]
        return self.task_pages.get(repo_path)

    def resolver(self, doc, here):
        """A link resolver for Markdown from repository file `doc` rendered
        into the page `here`."""
        repo_url = self.config.get("repo_url")

        def resolve(target):
            if target.startswith("site:"):        # site/content/ files link to pages directly
                return rel_link(here, target[len("site:"):])
            if re.match(r"^[a-z][a-z0-9+.-]*:", target):
                return target                     # https:, mailto:
            path, _, frag = target.partition("#")
            if not path:
                return "#" + frag
            repo = posixpath.normpath(posixpath.join(posixpath.dirname(doc), path))
            site_path = self.site_path_of(repo)
            if site_path is not None:
                return rel_link(here, site_path + ("#" + frag if frag else ""))
            self.unlinked.add(repo)
            url = repo_link(repo_url, repo)
            if url:
                return url + ("#" + frag if frag else "")
            return None
        return resolve

    def doc_text(self, rel):
        """A repository document with config.json's redactions applied, in
        order. A redaction whose text is not in the document exactly once (with
        `"all": true`: at least once, every occurrence replaced) is stale and
        fails the build."""
        text = read_text(rel)
        for r in self.config.get("redact", []):
            if r["file"] != rel:
                continue
            n = text.count(r["text"])
            if n == 0 or (n != 1 and not r.get("all")):
                raise BuildError(f"config.json redaction for {rel} is stale: its text occurs {n} times "
                                 f"(expected {'at least once' if r.get('all') else 'once'}): {r['text']!r}")
            text = text.replace(r["text"], r["with"])
        return text

    def render_md(self, text, *, source, here, first_line=1, slugger=None, heading_shift=0):
        return md.render(text, source=source, first_line=first_line, resolve_link=self.resolver(source, here),
                         highlight=_md_highlight, slugger=slugger, heading_shift=heading_shift)


def _md_highlight(code_text, lang):
    return highlight(code_text, language_of(lang))   # an unknown language comes back escaped, plain


def omit_sections(text, omit):
    """`text` with the sections whose heading is in `omit` blanked out
    (blanked, not removed, so that line numbers in errors stay right)."""
    lines = text.split("\n")
    for level, title, start, end in md.split_sections(text):
        if title in omit:
            lines[start:end] = [""] * (end - start)
    return "\n".join(lines)


def doc_sections(text, titles, omit=()):
    """The level-2 sections `titles` of a Markdown document, each as (title,
    text, first line number), without the sections named in `omit`."""
    secs = md.split_sections(text)
    lines = omit_sections(text, omit).split("\n")
    out = []
    for want in titles:
        hit = [s for s in secs if s[0] == 2 and s[1] == want]
        if len(hit) != 1:
            raise BuildError(f"expected one section '## {want}', found {len(hit)}")
        _, title, start, end = hit[0]
        out.append((title, "\n".join(lines[start:end]), start + 1))
    return out


# ---------------------------------------------------------------------------
# the data: tasks, references, baselines, attacks, records
# ---------------------------------------------------------------------------

def module_file(mod):
    """The repository path of a Lean module of the trusted closure, or None
    for a toolchain module (Init, Std, Lean, Lake)."""
    head = mod.split(".")[0]
    if head in ("SvGolf", "spec", "tasks"):
        return "svgolf/" + mod.replace(".", "/") + ".lean"
    if head == "LeanModels":
        return mod.replace(".", "/") + ".lean"
    if head in TOOLCHAIN_ROOTS:
        return None
    raise BuildError(f"the trusted closure reaches {mod}, which belongs to no known root")


def import_closure(module):
    """[(module, repository path or None)] reachable from `module` through
    `import`, computed from the sources (leaderboard.py's `lean_imports`
    reads the header the way Lean does). The module itself first, then the
    others by name; toolchain modules are not followed."""
    seen, todo = {}, [module]
    while todo:
        mod = todo.pop()
        if mod in seen:
            continue
        path = module_file(mod)
        seen[mod] = path
        if path is None:
            continue
        if not os.path.isfile(repo_file(path)):
            raise BuildError(f"{mod}: no source at {path}")
        todo.extend(lb.lean_imports(read_text(path)))
    rest = sorted(m for m in seen if m != module)
    return [(module, seen[module])] + [(m, seen[m]) for m in rest]


def module_role(mod):
    head = mod.split(".")[0]
    return {"tasks": "task statement", "SvGolf": "svGolf statement helpers", "spec": "IEEE 754 specification",
            "LeanModels": "ls-sv semantics"}.get(head, "Lean toolchain")


class Task:
    """Everything one task page shows."""

    def __init__(self, name, task, listing):
        self.name, self.task, self.listing = name, task, listing
        self.dir = f"svgolf/tasks/{name}"
        self.page = f"tasks/{name}/index.html"
        self.point = lb.scoring_point(task)
        self.point_key = point_key(self.point)
        self.spec = f"{self.dir}/Spec.lean"
        self.closure = import_closure(task["statement"]["module"])
        self.title, self.subtitle, self.banlist_note = task.get("title", name), "", None
        self.refs, self.baselines, self.rejects = [], [], []
        # records: all of the task's; the players' (ranked on `board`); the reference player's (par)
        self.records, self.player_records, self.ref_records = [], [], []
        self.board, self.full_board, self.par = None, None, None
        self.drive = None                         # the cell in front of every input of the sky130 score
        self.ref_of_record = {}                   # a reference player's record hash -> its reference
        self.number = None                        # "00" the tutorial, "01".. the listed tasks (`collect`)
        self.designs = []                         # every design the page compares (`task_designs`)
        self.props = None                         # properties.json, resolved (props.TaskProperties), or None
        self.preview_note = None                  # a preview's status line (content/tasks/<t>.json `preview_note`)
        self.measured = None                      # score/measured/<task>.json (metrics.load_measured), or None
        self.views = []                           # the explorer's points (`point_views`), the scored one first-class
        self.lines = []                           # the scaling view's lines (`scaling_lines`)

    @property
    def preview(self):
        """A preview: listed, its designs shown and measured, nothing ranked (no par, no record, no board)."""
        return self.listing == "preview"

    @property
    def kind(self):
        return self.task.get("kind", "")

    def ranked(self):
        """The players' ranked records (the reference player's are par, not entries)."""
        return self.board["frontier"] + self.board["dominated"]

    def best(self):
        """(the first row of the players' (sky130 area, time) frontier, the best time on it), or (None, None)."""
        front = self.board["frontier"]
        if not front:
            return None, None
        return front[0], min(r["time_ps"] for r in front)

    def solvers(self):
        return len({r["player"] for r in self.ranked()})


def score_at(entry, key):
    s = (entry.get("scores") or {}).get(key)
    return s if s and "area_mge" in s else None


def curated(site, t, table, key, what):
    """The curated public sentence `table[key]` for `what`, or "" (with a
    warning, fatal under --strict) when there is none."""
    text = (table or {}).get(key)
    if isinstance(text, str) and text.strip():
        return text.strip()
    site.warn(f"{t.name}: no public description of {what} in {CONTENT}/"
              + ("attacks" if what.startswith(("negative", "attack")) else "tasks") + f"/{t.name}.json")
    return ""


def stale_curated(site, t, table, known, where):
    for key in sorted(set(table or {}) - set(known)):
        site.warn(f"{t.name}: {CONTENT}/{where} describes {key!r}, which the task does not have")


def collect_task(site, name, task, listing, expected, records):
    t = Task(name, task, listing)
    exp = expected["tasks"].get(name, {})
    ref_player = site.config["reference_player"]
    # the public texts (never the internal notes of task.json and tests/expected.json)
    info = site.content(f"tasks/{name}.json")
    if info is None:
        site.warn(f"{name}: no {CONTENT}/tasks/{name}.json (display title, descriptions); "
                  "the task.json title is used")
        info = {}
    t.title = info.get("title") or task.get("title", name)
    t.subtitle = info.get("subtitle", "")
    t.banlist_note = info.get("banlist_note")
    if t.preview:
        note = info.get("preview_note")
        if not (isinstance(note, str) and note.strip()):
            raise BuildError(f"{name}: a preview needs `preview_note` in {CONTENT}/tasks/{name}.json, the status "
                             "line its pages show (why it is not ranked yet)")
        t.preview_note = note.strip()
    # records and the boards, under the pinned flow: the players' records are ranked, the reference
    # player's are par (shown with the proved references); `full_board` is leaderboard.py's own board
    # of every record, for the machine-readable output
    t.records = sorted((r for r in records if r["task"] == name), key=lambda r: lb.row_key(lb.row_of(r)))
    t.player_records = [r for r in t.records if r["player"] != ref_player]
    t.ref_records = [r for r in t.records if r["player"] == ref_player]
    # ranked on the sky130 A0' area and time, under the pinned flow, the repository's sky130 identity
    # (score/ppa_pins.json) and the task's input drive: leaderboard.py's own comparability rule
    t.drive = lb.ppa_setup_now(task).get("input_drive")
    t.board = lb.build_board(task, t.player_records, flow=site.flow, identity=site.ppa_identity, input_drive=t.drive)
    t.full_board = lb.build_board(task, t.records, flow=site.flow, identity=site.ppa_identity, input_drive=t.drive)
    for r in t.records:
        site.player_text.update([r["player"], *r.get("assisted_by", []), r.get("notes") or ""])
    # proved references: task.json lists them, expected.json scores them; a reference is matched to
    # the reference player's record of it by the sha256 of its design AND of its proof (one design
    # may ship with several proofs), never by file name
    for ref in task.get("references", []):
        stem = posixpath.splitext(posixpath.basename(ref["sv"]))[0]
        sv_rel, lean_rel = f"{t.dir}/{ref['sv']}", f"{t.dir}/{ref['lean']}"
        sv_bytes, lean_bytes = read_bytes(sv_rel), read_bytes(lean_rel)
        lean_text = lean_bytes.decode("utf-8")
        e = exp.get("references", {}).get(stem, {})
        s = score_at(e, t.point_key)
        sha, lean_sha = sha256(sv_bytes), sha256(lean_bytes)
        record = next((r for r in t.ref_records if r["files"]["sv"]["sha256"] == sha
                       and r["files"]["lean"]["sha256"] == lean_sha), None)
        t.refs.append({
            "stem": stem, "sv": sv_rel, "lean": lean_rel,
            "description": curated(site, t, info.get("references"), stem, f"the reference {stem}"),
            "sha256": sha, "same_design_as": e.get("same_design_as"), "score": s,
            "proof_lines": lb.lean_code_lines(lean_text), "tactics": lb.lean_tactics(lean_text),
            "record_hash": record["record_hash"] if record else None,
            "row": None if s is None else {"record_hash": sha, "player": "", "submitted_at": "",
                                           "area_mge": s["area_mge"], "depth": s["depth"]}})
        if record:
            t.ref_of_record[record["record_hash"]] = t.refs[-1]
    stale_curated(site, t, info.get("references"), [r["stem"] for r in t.refs], f"tasks/{name}.json (references)")
    for r in t.ref_records:
        if r["record_hash"] not in t.ref_of_record:
            site.warn(f"{name}: record {r['record_hash'][:12]} of the reference player is not one of the task's "
                      "proved references (design and proof): it is shown on no table")
    # baselines: scored, never accepted
    for stem, e in exp.get("baselines", {}).items():
        t.baselines.append({"stem": stem, "sv": f"svgolf/tests/{name}/" + e.get("sv", f"baselines/{stem}.sv"),
                            "banned": bool(e.get("banned")),
                            "description": curated(site, t, info.get("baselines"), stem, f"the baseline {stem}"),
                            "score": score_at(e, t.point_key),
                            "points": sorted(k for k in (e.get("scores") or {}) if k != t.point_key)})
    t.baselines.sort(key=lambda b: (b["score"] is None, (b["score"] or {}).get("area_mge", 0),
                                    (b["score"] or {}).get("depth", 0), b["stem"]))
    stale_curated(site, t, info.get("baselines"), [b["stem"] for b in t.baselines], f"tasks/{name}.json (baselines)")
    # par: the proved reference with the best combined score (area x time); one without a sky130
    # weighing comes after every one with it, then area and depth decide. The board's later keys
    # (date, player, hash) mean nothing for a design that is not a record, so equal scores fall back
    # to the order in which task.json lists its references (the first is the task's primary one).
    t.designs = task_designs(site, t)
    exact = {d["stem"]: d["exact"] for d in t.designs if d["kind"] == "reference"}
    scored = [(k, r) for k, r in enumerate(t.refs) if r["row"]]
    if t.preview:
        pass                                     # a preview has no par: nothing of it is ranked
    elif scored:
        t.par = min(scored, key=lambda kr: (exact.get(kr[1]["stem"]) is None, exact.get(kr[1]["stem"]) or 0,
                                            kr[1]["row"]["area_mge"], kr[1]["row"]["depth"], kr[0]))[1]
    elif task.get("status") == "ready":
        site.warn(f"{name}: no proved reference has a score at {t.point_key} in tests/expected.json")
    for d in t.designs:
        d["par"] = bool(t.par) and d["kind"] == "reference" and d["stem"] == t.par["stem"]
    # the other points the designs are measured at (score/measured/<task>.json): the explorer's
    # point selector and the scaling view; measured, never ranked
    t.measured = metrics.load_measured(name, site.ppa_identity, t.drive, warn=site.warn)
    t.views, t.lines = point_views(t), scaling_lines(t)
    # what does not count: negatives and the attacks that are not advisory checks, each with its
    # curated sentence (content/attacks/<t>.json)
    said = site.content(f"attacks/{name}.json") or {}
    for kind, section, subdir in (("negative", "negatives", "negative"), ("attack", "attacks", "attacks")):
        mine = []
        for stem, e in sorted(exp.get(section, {}).items()):
            if e.get("advisory") or e.get("stage") == "unproved":
                continue                         # not rejected: a check of the checker, or a correct design
            mine.append(stem)
            t.rejects.append({"kind": kind, "stem": stem, "stage": e["stage"],
                              "description": curated(site, t, said.get(section), stem, f"{kind} {stem}"),
                              "sv": f"svgolf/tests/{name}/" + e.get("sv", f"{subdir}/{stem}.sv")})
        stale_curated(site, t, said.get(section), mine, f"attacks/{name}.json ({section})")
    order = {s: k for k, s in enumerate(site.stages)}
    t.rejects.sort(key=lambda r: (order.get(r["stage"], len(order)), r["kind"], r["stem"]))
    t.props = load_properties(t)
    return t


def properties_page(t):
    """The source view of a task's Properties.lean."""
    return f"tasks/{t.name}/properties.html"


def load_properties(t):
    """The task's properties.json and Properties.lean, resolved and checked (props.load), or None."""
    by_path = {p: m for m, p in t.closure if p}

    def source_page(path, decl):
        if path == f"{t.dir}/Properties.lean":
            return f"{properties_page(t)}#{decl}"
        return f"{trusted_page(by_path[path])}#{decl}"

    try:
        return props.load(t.name, t.dir, t.task["statement"]["constant"], t.closure, read_text, source_page,
                          lambda rel: os.path.isfile(repo_file(rel)))
    except props.PropsError as e:
        raise BuildError(str(e))


def collect(site, offline):
    """All listed tasks, in display order: the order of config.json's `tasks`."""
    expected = json.loads(read_text("svgolf/tests/expected.json"))
    pin = expected["flow"]
    site.flow = {"yosys": pin["yosys_version"], "canon_script_sha256": pin["canon_script_sha256"],
                 "script_sha256": pin["script_sha256"], "ge_table_sha256": pin["ge_table_sha256"]}
    site.ppa_identity = lb.ppa_identity()          # score/ppa_pins.json: a repository file, no liberty needed
    if not offline:
        now = lb.current_flow(SVGOLF)
        bad = sorted(k for k, v in site.flow.items() if now.get(k) is None or now[k] != v)
        if bad:
            raise BuildError("the machine's scoring flow differs from the pin in tests/expected.json on "
                             + ", ".join(f"{k} ({now.get(k)!r} here)" for k in bad)
                             + "; build with --offline to skip this check")
    loaded = lb.load_records(os.path.join(SVGOLF, "leaderboard", "data"))
    records = lb.good_records(loaded, warn=site.warn)
    listing = site.config["tasks"]                 # (task names may start with `_`: `_example`)
    tasks_dir = os.path.join(SVGOLF, "tasks")
    on_disk = lb.all_task_names(tasks_dir)
    unknown = sorted(set(listing) - set(on_disk))
    if unknown:
        raise BuildError(f"config.json lists tasks that do not exist: {', '.join(unknown)}")
    order = {name: k for k, name in enumerate(listing)}
    out = []
    for name in sorted(on_disk, key=lambda n: (order.get(n, len(order)), n)):
        how = listing.get(name)
        if how is None:
            site.warn(f"task {name} is not in config.json `tasks`: hidden")
            how = "hidden"
        if how not in ("tutorial", "listed", "preview", "hidden"):
            raise BuildError(f"config.json: task {name}: listing {how!r} is not tutorial, listed, preview or hidden")
        if how == "hidden":
            continue
        out.append(collect_task(site, name, lb.load_task(tasks_dir, name), how, expected, records))
    listed = [t for t in out if t.listing == "listed"] + [t for t in out if t.listing == "preview"]
    for k, t in enumerate(listed, 1):
        t.number = f"{k:02d}"
    for t in out:
        if t.listing == "tutorial":
            t.number = "00"
    for t in out:
        site.task_pages[f"{t.dir}/README.md"] = t.page
        site.task_pages[t.spec] = t.page + "#spec"
        if t.props:
            site.task_pages[t.props.file] = properties_page(t)
    return out


# ---------------------------------------------------------------------------
# task pages
# ---------------------------------------------------------------------------

def compact_ge(mge):
    """An area for a big number: GE without trailing zeros ('112', '127.658')."""
    s = lb.fmt_ge(mge)
    return s.rstrip("0").rstrip(".") if "." in s else s


def status_badge(task, listing=None):
    """The badge "open for submissions" for a task whose statement and checker are final (status
    `ready`), else its status; a preview's says that it is not ranked."""
    if listing == "preview":
        return page.badge("preview: not ranked", "draft")
    if task.get("status") == "ready":
        return page.badge("open for submissions", "open")
    return page.badge(task.get("status", "unknown"), "draft")


def file_links(here, base, exts):
    """Download links to `base` + each extension, labelled by the extension."""
    return " ".join(page.link(rel_link(here, base + ext), ext) for ext in exts)


def players(n):
    return f"{n} player" + ("" if n == 1 else "s")


# ---------------------------------------------------------------------------
# the designs a task page compares, and the combined score
# ---------------------------------------------------------------------------

KIND_TEXT = {"record": "submission", "reference": "proved reference", "baseline": "baseline, not proved"}


def task_designs(site, t):
    """Every design the task page compares, one dict each: the proved references, the players'
    ranked records and the baselines that have a score at the scoring point. Keys: id (unique on
    the page), kind (reference | record | baseline), stem (a reference's or baseline's name), name,
    sha (of the design file), date (a record's submission date; a reference's is the date of the
    last commit that changed its design, `metrics.commit_date`; a baseline has none), href (where
    its mark links: a record's page, a reference's or baseline's row on the page), banned, layer (a
    record's Pareto layer on the (sky130 area, time) board), m (its metrics, `metrics.design_metrics`) and
    exact (its combined score as an exact integer, or None without a sky130 weighing). `par` is set
    by `collect_task` once par is known."""
    sky = site.sky130()
    out = []
    for ref in t.refs:
        s = ref["score"]
        if not s:
            continue
        rec = next((r for r in t.ref_records if r["record_hash"] == ref["record_hash"]), None)
        gold = sky.of_file(t.name, t.point, repo_file(ref["sv"]))
        # no golden: the sky130 columns of the reference's own record, when they are comparable (the
        # current flow, point, sky130 identity and the task's input drive: leaderboard.py's rule)
        own = (rec.get("ppa") if gold is None and rec is not None and not lb.unranked_reason(
            rec, t.task, flow=site.flow, identity=site.ppa_identity, input_drive=t.drive) else None)
        m, exact = metrics.design_metrics(s, sky=gold, ppa=own,
                                          energy=sky.energy_of(t.name, ref["stem"], t.point_key),
                                          proof_lines=ref["proof_lines"])
        out.append({"id": f"reference/{ref['stem']}", "kind": "reference", "stem": ref["stem"], "name": ref["stem"],
                    "sha": ref["sha256"], "date": metrics.commit_date(repo_file(ref["sv"])) or (rec or {}).get("submitted_at"),
                    "href": f"#ref-{ref['stem']}", "banned": False, "m": m, "exact": exact, "par": False})
    for r in t.ranked():
        rec = next(x for x in t.player_records if x["record_hash"] == r["record_hash"])
        m, exact = metrics.design_metrics(rec["score"], ppa=rec.get("ppa"), proof_lines=r["proof_lines"],
                                          sky=sky.of_rtlil(t.name, t.point, rec["score"].get("rtlil_sha256")))
        out.append({"id": r["record_hash"], "kind": "record", "stem": None, "name": r["player"],
                    "sha": rec["files"]["sv"]["sha256"], "date": r["submitted_at"], "layer": r["layer"],
                    "href": f"records/{r['record_hash']}.html", "banned": False, "m": m, "exact": exact,
                    "par": False, "light": r.get("postsynth") == "light"})
    for b in t.baselines:
        if not b["score"]:
            continue
        m, exact = metrics.design_metrics(b["score"], sky=sky.of_file(t.name, t.point, repo_file(b["sv"])),
                                          energy=sky.energy_of(t.name, b["stem"], t.point_key))
        out.append({"id": f"baseline/{b['stem']}", "kind": "baseline", "stem": b["stem"], "name": b["stem"],
                    "sha": sha256(read_bytes(b["sv"])), "date": None, "href": f"#baseline-{b['stem']}",
                    "banned": b["banned"], "m": m, "exact": exact, "par": False})
    # a design file shared by two entries (a second proof of a reference) has one energy figure
    energy = {}
    for d in out:
        for k in ("energy_fj", "energy_cycle_fj", "leakage_nw"):
            if k in d["m"]:
                energy.setdefault(d["sha"], {}).setdefault(k, d["m"][k])
    for d in out:
        for k, v in energy.get(d["sha"], {}).items():
            d["m"].setdefault(k, v)
    return out


MEASURED = "measured, not ranked"
DESIGN_ORDER = {"reference": 0, "baseline": 1, "record": 2}


def point_names(t, p):
    """(short, full) names of a point of score/measured/<task>.json, its parameters in task.json's
    order: ('N = 8', 'N = 8'), ('binary32', 'binary32 (W = 8, P = 24)')."""
    text = point_text({k: p["params"][k] for k in t.point if k in p["params"]})
    return (p["label"], f"{p['label']} ({text})") if p.get("label") else (text, text)


def measured_design(t, e, key):
    """The design `e` of score/measured/<task>.json at the point `key`, as `task_designs` writes a
    design: its metrics from the measured row (`metrics.measured_metrics`), its link the same as at
    the scored point, `measured` set."""
    refs = {r["stem"]: r for r in t.refs}
    if e["kind"] == "reference":
        href, proof = f"#ref-{e['name']}", (refs.get(e["name"]) or {}).get("proof_lines")
    elif e["kind"] == "baseline":
        href, proof = f"#baseline-{e['name']}", None
    else:
        pages = {r["record_hash"] for r in t.player_records}
        href, proof = (f"records/{e['id']}.html" if e["id"] in pages else None), None
    m, exact = metrics.measured_metrics(e["at"][key], proof_lines=proof)
    return {"id": e["id"], "kind": e["kind"], "stem": e["name"] if e["kind"] != "record" else None,
            "name": e["name"], "sha": e["sha256"], "date": None, "href": href, "banned": e["banned"], "m": m,
            "exact": exact, "par": False, "measured": True}


def point_views(t):
    """The points the explorer offers, in the order of the task's scaling parameter: {key, short,
    full, x, scored, designs}. The scored point's designs are the page's own (`task_designs`: the
    ranked numbers); every other point's are measured (score/measured/<task>.json, the same pinned
    flow at other parameters), never ranked. One view (the scored point) without measured data."""
    own = {"key": t.point_key, "short": point_text(t.point), "full": point_text(t.point), "x": None, "scored": True,
           "designs": t.designs}
    if not t.measured:
        return [own]
    views = []
    for p in t.measured["points"]:
        short, full = point_names(t, p)
        if p["key"] == t.point_key:
            views.append(dict(own, short=short, full=full, x=p["x"]))
            continue
        ds = [measured_design(t, e, p["key"]) for e in t.measured["designs"] if p["key"] in e["at"]]
        if ds:
            views.append({"key": p["key"], "short": short, "full": full, "x": p["x"], "scored": False, "designs": ds})
    return views


def scaling_lines(t):
    """The scaling view's lines, one per design, from score/measured/<task>.json: {id, kind, banned,
    name (the label), names (every design the line stands for), href, pts: [{key, x, m}] by x}. A
    family of fixed-size baselines (points.json `families`, one file per size) is one line under the
    family's name; designs with the same numbers at every point (a reference with a second proof, or
    written another way that the flow makes the same circuit) share one line, named by the first in
    task.json's order with the count of the others. The scored point's numbers are the measured ones there (score/test_points.py:
    equal to the goldens)."""
    if not t.measured or len(t.measured["points"]) < 2:
        return []
    xs = {p["key"]: p["x"] for p in t.measured["points"]}
    ref_order = {r["stem"]: k for k, r in enumerate(t.refs)}
    groups = {}
    for e in sorted(t.measured["designs"], key=lambda e: (DESIGN_ORDER[e["kind"]], ref_order.get(e["name"], 99),
                                                           e["name"], e["id"])):
        if not e["at"]:
            continue
        if e["kind"] == "baseline" and e["family"] != e["name"]:
            gk = ("family", e["family"])
        else:
            gk = ("same", e["kind"], e["banned"], tuple((k, r["area_e4um2"], r.get("time_ps"), r["area_mge"], r["depth"],
                                                         r["num_gates"]) for k, r in sorted(e["at"].items())))
        groups.setdefault(gk, []).append(e)
    lines = []
    for gk, members in groups.items():
        first = members[0]
        pts = {}
        for e in members:
            for key in e["at"]:
                pts.setdefault(key, measured_design(t, e, key))
        family = gk[0] == "family"
        names = [e["name"] for e in members]
        lines.append({"id": f"line/{first['id']}", "ids": [e["id"] for e in members], "kind": first["kind"],
                      "banned": first["banned"],
                      "name": first["family"] if family else first["name"] + (f" +{len(names) - 1}" if len(names) > 1 else ""),
                      "names": names, "family": family, "href": pts[min(pts, key=lambda k: xs[k])]["href"],
                      "pts": [{"key": k, "x": xs[k], "m": pts[k]["m"]} for k in sorted(pts, key=lambda k: xs[k])]})
    return lines


def score_key(d):
    """The leaderboard's order: the combined score (a design without one after every design with
    it), then area and depth in GE, then the earlier date, then the id."""
    return (d["exact"] is None, d["exact"] or 0, d["m"]["area_ge"], d["m"]["depth"], d["date"] or "~", d["id"])


def entries(t):
    """The entries the record is taken over, with a score: the proved references (the first
    entries; one per design, a second proof of the same design is not a new score) and the players'
    ranked records."""
    out, seen = [], set()
    for d in sorted((d for d in t.designs if d["kind"] == "reference" and d["exact"] is not None),
                    key=lambda d: (d["date"] or "~", [r["stem"] for r in t.refs].index(d["stem"]))):
        if d["sha"] not in seen:
            seen.add(d["sha"])
            out.append(d)
    return out + [d for d in t.designs if d["kind"] == "record" and d["exact"] is not None]


def par_design(t):
    return next((d for d in t.designs if d["par"]), None)


def headline(t):
    """A task's three big numbers (the page head, the home page's task cards): {"par", "record",
    "under", "unit", "par_name", "record_name"}, scores in the display unit (combined.UNIT). PAR is
    the best proved reference's score; RECORD the best entry's (`entries`: the proved references
    count as the first entries, so with no submission the record is par); UNDER how far the record
    is below par, as a fraction. All None when par has no sky130 weighing."""
    p = par_design(t)
    es = entries(t)
    if p is None or p["exact"] is None or not es:
        return {"par": None, "record": None, "under": None, "unit": combined.UNIT, "par_name": None,
                "record_name": None, "par_design": None, "record_design": None}
    best = min(es, key=lambda d: (d["exact"], d["date"] or "~", d["id"]))
    return {"par": p["m"]["adp"], "record": best["m"]["adp"], "under": (p["exact"] - best["exact"]) / p["exact"],
            "unit": combined.UNIT, "par_name": p["name"], "record_name": best["name"], "par_design": p,
            "record_design": best}


def under_text(under):
    """'−68%' for a record 68% under par; '0%' at par."""
    if under is None:
        return "–"
    pct = round(under * 100)
    return "0%" if pct == 0 else f"−{pct}%" if pct > 0 else f"+{-pct}%"


def big_numbers(t, *, notes=True):
    """The big numbers of `headline`: PAR, RECORD, UNDER PAR (zk.golf's three)."""
    h = headline(t)
    if h["par"] is None:
        return page.stats([page.Stat("Par", "–", kind="empty"),
                           page.Stat("Record", "–", kind="empty"), page.Stat("Under par", "–", kind="empty")])

    def note(name, d):
        """The design's name and its two ranked numbers, area × time ('add_n · 460.4 µm² × 2.59 ns')."""
        return f"{name} · {breakdown(d)}" if d and breakdown(d) else name
    return page.stats([
        page.Stat("Par", combined.fmt(h["par"]), unit=h["unit"], note=note(h["par_name"], h["par_design"]) if notes else None),
        page.Stat("Record", combined.fmt(h["record"]), unit=h["unit"],
                  note=note(h["record_name"], h["record_design"]) if notes else None),
        page.Stat("Under par", under_text(h["under"]), kind="accent" if h["under"] and h["under"] > 0 else None)])


def ns(ps):
    """Picoseconds as nanoseconds with three significant digits: '2.60', '10.7', '378'."""
    v = ps / 1000
    return f"{v:.2f}" if v < 10 else f"{v:.1f}" if v < 100 else f"{v:.0f}"


def breakdown(d):
    """A score's factors as text: '460.4 µm² × 2.60 ns', a clocked one '87 174 µm² × 4 × 10.7 ns'."""
    m = d["m"]
    if "area_um2" not in m or "time_ps" not in m:
        return ""
    area = f"{m['area_um2']:,.0f}".replace(",", "\u202f") if m["area_um2"] >= 10000 else f"{m['area_um2']:.1f}"
    if "cycles" in m and "period_ps" in m:
        return f"{area} µm² × {m['cycles']} × {ns(m['period_ps'])} ns"
    return f"{area} µm² × {ns(m['time_ps'])} ns"


def statement_html(site, t, here, slugger):
    path = f"{CONTENT}/tasks/{t.name}.md"
    if os.path.isfile(repo_file(path)):
        return site.render_md(read_text(path), source=path, here=here, slugger=slugger, heading_shift=1).html
    msg = f"{t.name}: no {path}; the task page uses the README's introduction instead"
    if site.strict:
        raise BuildError(msg)
    site.warn(msg)
    readme = f"{t.dir}/README.md"
    text = site.doc_text(readme)
    secs = md.split_sections(text)
    start = secs[0][2] + 1 if secs and secs[0][0] == 1 else 0
    end = next((s[2] for s in secs if s[0] == 2), len(text.split("\n")))
    intro = "\n".join(text.split("\n")[start:end])
    return site.render_md(intro, source=readme, here=here, first_line=start + 1, slugger=slugger).html


def circuit_header(site, t):
    """The first SystemVerilog block of the README's `## The circuit` section."""
    readme = f"{t.dir}/README.md"
    text = site.doc_text(readme)
    for level, title, start, end in md.split_sections(text):
        if level == 2 and title == "The circuit":
            body = "\n".join(text.split("\n")[start:end])
            m = re.search(r"^```(?:systemverilog|sv|verilog)[ \t]*\n(.*?)\n```", body, re.S | re.M)
            if m:
                return m.group(1)
    site.warn(f"{t.name}: no SystemVerilog block under '## The circuit' in {readme}")
    return None


def interface_html(site, t):
    task = t.task
    parts = []
    header = circuit_header(site, t)
    if header:
        parts.append("<p>Write a module with exactly this header: port names, directions, widths and order "
                     "matter, and so do the module's name and its parameters.</p>")
        parts.append(page.code_block(header, "sv", name=f"{task['top']}.sv"))
    ports = task.get("ports", {})
    rows = [[code(p["name"]), "input", esc(p["width"])] for p in ports.get("inputs", [])]
    rows += [[code(p["name"]), "output", esc(p["width"])] for p in ports.get("outputs", [])]
    parts.append(page.table(["port", "direction", "width (bits)"], rows))
    return "\n".join(parts)


def facts_html(t):
    """The task at a glance: top module, parameters, scoring point, budgets, banlist, axioms."""
    task = t.task
    facts = [("top module", code(task["top"]))]
    if task.get("parameters"):
        facts.append(("parameters", ", ".join(f"{code(p['name'])} in range {code(p['range'])}"
                                              for p in task["parameters"])))
    else:
        facts.append(("parameters", "none: one fixed size"))
    facts.append(("scoring point", esc(point_text(t.point))))
    budget = lb.effective_depth_budget(task)
    facts.append(("depth budget", esc(budget) if budget is not None else "none"))
    ops = task.get("banlist", {}).get("operators", [])
    banned = " ".join(code(o) for o in ops) if ops else "none"
    comment = t.banlist_note or task.get("banlist", {}).get("_comment")
    facts.append(("banned run-time operators", banned + (f'<p class="muted">{md_inline(comment)}</p>' if comment else "")))
    facts.append(("allowed axioms", ", ".join(code(a) for a in task.get("allowed_axioms", []))))
    facts.append(("proof time limit", esc(f"{task.get('time_limit_s')} s")))
    return page.dl(facts)


def line_count(text):
    return text.count("\n") + (0 if text.endswith("\n") or not text else 1)


def spec_summary(spec_text):
    """The parts of a Spec.lean the statement card shows: the `Statement:` paragraph of its module
    docstring (prose) and the declaration of `Statement` with its docstring (Lean), each or None."""
    lines = spec_text.split("\n")
    prose = None
    for k, ln in enumerate(lines):
        if ln.startswith("Statement:"):
            end = next((j for j in range(k, len(lines)) if not lines[j].strip() or lines[j].startswith("-/")), len(lines))
            prose = " ".join(x.strip() for x in lines[k:end])[len("Statement:"):].strip()
            break
    decl = None
    at = next((k for k, ln in enumerate(lines) if re.match(r"^(abbrev|def) Statement\b", ln)), None)
    if at is not None:
        start = at
        if at > 0 and lines[at - 1].rstrip().endswith("-/"):
            start = next((j for j in range(at - 1, -1, -1) if lines[j].lstrip().startswith("/--")), at)
        end = next((j for j in range(at, len(lines)) if not lines[j].strip()), len(lines))
        decl = "\n".join(lines[start:end])
    return prose, decl


def properties_html(t, here):
    """The property panel (props.py): one card per property a circuit must have (a plain-English
    paragraph, its Lean text cut from Properties.lean, its file and a link into the source view),
    the definitions they use, and the theorem that makes the cards exactly the trusted statement.
    A task without a properties.json gets one card, the statement as a whole (its own prose and
    declaration, from Spec.lean)."""
    if t.props:
        return props.panel(t.props, task_dir=t.dir, proved=None, rejected=len(t.rejects),
                           link=lambda target: rel_link(here, target), md_inline=md_inline)
    prose, decl = spec_summary(read_text(t.spec))
    name = t.task["statement"]["constant"].rsplit(".", 1)[-1]
    body = (f"<p>{md_inline(prose[:1].upper() + prose[1:])}</p>" if prose else "")
    if decl:
        body += page.code_block(decl, "lean", name=name, cls="code excerpt")
    href = rel_link(here, trusted_page(t.task["statement"]["module"]))
    body += (f'<div class="prop-path"><span>{esc(t.spec)}</span>'
             + page.button(href, "Open in code", "quiet sm", arrow=True) + "</div>")
    card = page.prop_card(re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "_", name).upper(),
                          status=None, body_html=body, id_="prop-statement", open_=True)
    return page.props_panel([("props-properties", "Properties", 1, card)], hook="properties")


def spec_html(t, here):
    spec_text = read_text(t.spec)
    spec_link = page.link(rel_link(here, f"tasks/{t.name}/Spec.lean"), code("Spec.lean"))
    split = (" Below it is split into the properties a circuit must have, one card each: what the property "
             "guarantees in plain words, and its exact Lean text. Every proved reference has all of them."
             if t.props else " The proved references meet it.")
    parts = [f"<p>A proof must establish the task's trusted statement, the constant "
             f"{code(t.task['statement']['constant'])} of {spec_link} (module {code(t.task['statement']['module'])})."
             f"{split}</p>",
             properties_html(t, here),
             page.details(f"{code('Spec.lean')}, verbatim ({line_count(spec_text)} lines)",
                          page.code_block(spec_text, "lean", src=t.spec))]
    own = [(mod, path) for mod, path in t.closure if path is not None and not is_shared_trusted(mod)]
    rows = []
    for mod, path in own:            # the file under the module's name: the task column is narrow
        cells = trusted_row(mod, path, here)
        rows.append([design_cell(cells[0], "", f'<span class="cell-meta">{esc(path)}</span>')] + cells[1:2] + cells[3:])
    parts.append("<h4 id=\"closure\">Its trusted text</h4>")
    parts.append("<p>The modules specific to this task. Like every task, it also rests on the "
                 + page.link(rel_link(here, SHARED_TRUSTED_PAGE), "shared trusted base")
                 + " (the ls-sv semantics of SystemVerilog and svGolf's statement helpers), and a proof may "
                 "import any module of the ls-sv library. Nothing else is trusted: proof helpers are "
                 "kernel-checked like any submission.</p>")
    parts.append(page.table(["module", "role", "lines", "sha256"], rows, numeric=(2,), cls="closure", stack=True))
    return "\n".join(parts)


SHARED_TRUSTED_PAGE = "trusted/index.html"


def is_shared_trusted(mod):
    """The trusted modules every task shares (the ls-sv semantics, svGolf's statement helpers), as opposed to a
    task's own statement and specification."""
    return mod.split(".")[0] in ("LeanModels", "SvGolf")


def trusted_row(mod, path, here):
    text = read_text(path)
    return [page.link(rel_link(here, trusted_page(mod)), code(mod)), esc(module_role(mod)),
            code(path), str(line_count(text)), code(sha256(text.encode("utf-8"))[:12])]


def trusted_page(mod):
    return f"trusted/{mod}.html"


def legend_html(kinds, *, front=None, par=False, levels=False):
    """A chart's legend: the kinds of mark it shows (`kinds`: a set of record, reference, baseline,
    banned) and its lines (`front`: the step line's meaning, `par`, `levels`)."""
    items = []
    if "record" in kinds:
        items.append(svgplot.legend_icon("record") + "submission")
    if "reference" in kinds:
        items.append(svgplot.legend_icon("reference") + "proved reference")
    if "baseline" in kinds:
        items.append(svgplot.legend_icon("baseline") + "baseline (not proved)")
    if "banned" in kinds:
        items.append(svgplot.legend_icon("baseline", banned=True) + "baseline with a banned operator")
    if front:
        items.append(svgplot.line_icon("frontier") + esc(front))
    if par:
        items.append(svgplot.line_icon("par-line") + "par")
    if levels:
        items.append(svgplot.line_icon("level") + "a baseline's score (not proved)")
    return '<ul class="legend">' + "".join(f"<li>{k}</li>" for k in items) + "</ul>"


def record_link(t, here, h, text_html=None):
    return page.link(rel_link(here, f"tasks/{t.name}/records/{h}.html"), text_html or code(h[:12]))


def assisted(row):
    return esc("; ".join(row["assisted_by"])) if row["assisted_by"] else '<span class="muted">none</span>'


def task_metrics(t):
    """The metrics (metrics.Metric) the task's designs have, at the scored point or a measured one,
    in the explorer's order."""
    have = {k for d in t.designs for k in d["m"]} | {k for v in t.views for d in v["designs"] for k in d["m"]}
    return [m for m in metrics.metric_table(metrics.is_clocked(t.task), metrics.input_drive(t.task)) if m.key in have]


def kind_text(d):
    text = KIND_TEXT[d["kind"]]
    if d["par"]:
        text += " · par"
    if d["banned"]:
        text += " · banned operator"
    if d.get("measured"):
        text += " · " + MEASURED
    return text


def tip_lines(d, ms):
    """A design's tooltip: its name, its kind, then `ms` (metrics.Metric) with their values."""
    out = [d["name"], kind_text(d) + (f" · {d['date']}" if d["date"] else "")]
    for m in ms:
        if m.key in d["m"]:
            out.append(f"{m.label}: {m.fmt(d['m'][m.key])}" + (f" {m.unit}" if m.unit else ""))
    return out


def mark_attrs(d):
    """The data attributes of a design's mark: its id, and a record's board numbers (the tests
    compare them with leaderboard.py's board)."""
    a = {"id": d["id"]}
    if d["kind"] == "record":
        a.update({"hash": d["id"], "area-mge": round(d["m"]["area_ge"] * 1000), "depth": d["m"]["depth"],
                  "frontier": "true" if d.get("layer") == 1 else "false"})
    return a


def page_data(t):
    """The task page's data for charts.js (inert JSON in `#task-data`): the metrics, every design
    with its metrics, and the explorer's first axes. Sorted keys, so two builds are identical."""
    ms = task_metrics(t)
    x, y = explorer_axes(t, ms)

    def one(d):
        return {"id": d["id"], "kind": d["kind"], "name": d["name"], "href": d["href"], "date": d["date"],
                "par": d["par"], "banned": d["banned"], "m": d["m"], **({"measured": True} if d.get("measured") else {})}
    out = {"task": t.name, "point": t.point, "unit": combined.UNIT,
           "metrics": [m.data() for m in ms], "axes": {"x": x, "y": y},
           "designs": [one(d) for d in t.designs]}
    if len(t.views) > 1:
        out["points"] = [{"key": v["key"], "short": v["short"], "full": v["full"], "scored": v["scored"]}
                         for v in t.views]
        if t.preview:
            out["preview"] = True                 # nothing of it is ranked: charts.js's point note says so
        out["at"] = {v["key"]: [one(d) for d in v["designs"]] for v in t.views if not v["scored"]}
    if t.lines:
        sm = scaling_metrics(t)
        pl = par_line(t)
        out["scaling"] = {"x_label": t.measured["scale"]["label"], "x_param": t.measured["scale"]["param"],
                          "ticks": scale_ticks(t), "metrics": [m.key for m in sm], "y": sm[0].key,
                          "par": pl["id"] if pl else None, "par_name": t.par["stem"] if pl else None,
                          "scored": t.point_key, "points": {v["key"]: v["full"] for v in t.views},
                          "lines": [{k: ln[k] for k in ("id", "kind", "banned", "name", "names", "family", "href")}
                                    | {"pts": [{"key": p["key"], "x": p["x"], "m": p["m"]} for p in ln["pts"]]}
                                    for ln in t.lines]}
    return out


def data_script(obj, id_):
    """JSON data for a page's script, inert as HTML (`</` cannot close the element)."""
    text = json.dumps(obj, sort_keys=True, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    return f'<script type="application/json" id="{esc(id_)}">{text}</script>'


def score_definition(t):
    clocked = metrics.is_clocked(t.task)
    time = ("the latency in cycles × the register-to-register clock period" if clocked
            else "the critical-path delay")
    return (f"<strong>Score</strong> = area × time: the sky130 cell area of the scored netlist in µm² "
            f"{'(flip-flops included) ' if clocked else ''}times {time} in ns, from the pinned flow, so "
            f"{esc(combined.UNIT)}. Lower is better; the leaderboard ranks the area and the time. Area in GE, "
            f"depth and the other numbers are under {page.link('#explore', 'compare the designs')}; "
            f"{page.link(rel_link(t.page, REPRODUCE_PAGE), 'reproduce a score')} says how to get the same numbers.")


def score_html(site, t, here):
    """The score card's body: the combined score over time (svgplot.score_chart, on a linear and a
    log axis; charts.js switches), its legend and definition, and every entry by date as a table.
    With no weighed design, what the score will start from."""
    if t.preview:
        return (f'<div class="chart-slot empty" id="over-time" data-hook="score-chart"><p>This task is a preview: '
                f"nothing of it is ranked yet, so no score history is drawn. Its designs are measured under "
                f"{page.link('#explore', 'compare the designs')}.</p><p class=\"small\">{score_definition(t)}</p></div>")
    es = entries(t)
    lv = [d for d in t.designs if d["kind"] == "baseline" and d["exact"] is not None]
    ms = [m for m in task_metrics(t) if m.key in ("adp", "area_um2", "time_ps")]
    if not es:
        p = par_design(t)
        start = (f"Par is the proved reference {code(t.par['stem'])}, with no sky130 weighing yet (its extra GE "
                 f"columns: {esc(ge(t.par['score']['area_mge']))}, depth {t.par['score']['depth']})." if p
                 else "There is no par yet.")
        return (f'<div class="chart-slot empty" id="over-time" data-hook="score-chart"><p>No design of this task '
                f"has a sky130 weighing yet, so the chart has nothing to draw: the score needs the sky130 area and "
                f"time. {start}</p><p class=\"small\">{score_definition(t)}</p></div>")
    p = par_design(t)
    par = {"value": p["m"]["adp"], "label": f"par: {p['name']}, {combined.fmt(p['m']['adp'])} {combined.UNIT}"} \
        if p and p["exact"] is not None else None
    pts = [{"id": d["id"], "kind": d["kind"], "date": d["date"], "value": d["m"]["adp"], "score": d["exact"],
            "tip": tip_lines(d, ms), "href": d["href"], "attrs": mark_attrs(d)} for d in es]
    levels = [{"id": d["id"], "name": d["name"], "value": d["m"]["adp"], "banned": d["banned"],
               "tip": tip_lines(d, ms)} for d in lv]
    until = max([d["date"] for d in t.designs if d["date"]] + [as_of() or ""])
    svgs = {(log, compact): svgplot.score_chart(
                pts, par=par, levels=levels, log=log, unit=combined.UNIT, value_fmt=combined.fmt,
                until=until or None, compact=compact,
                title=f"{t.name}: the score of each entry by date" + (", log scale" if log else ""))
            for log in (False, True) for compact in (False, True)}
    if not svgs[(False, False)]:
        return ('<div class="chart-slot empty" id="over-time" data-hook="score-chart"><p>No entry has a date: '
                "the history of this task cannot be drawn here.</p></div>")
    undated = [d for d in es if not d["date"]]
    rows = []
    for d in sorted(es, key=lambda d: (d["date"] or "~", d["exact"], d["id"])):
        rows.append([esc(d["date"] or "–"), page.link(d["href"], esc(d["name"])), esc(kind_text(d)),
                     esc(combined.fmt(d["m"]["adp"])), esc(breakdown(d))])
    for d in lv:
        rows.append(['<span class="muted">–</span>', page.link(d["href"], esc(d["name"])), esc(kind_text(d)),
                     esc(combined.fmt(d["m"]["adp"])), esc(breakdown(d))])
    variants = "".join(
        f'<div class="chart-variant" data-scale="{"log" if log else "linear"}" '
        f'data-size="{"compact" if compact else "wide"}"{" hidden" if log else ""}>{svgs[(log, compact)]}</div>'
        for log in (False, True) for compact in (False, True))
    named = ""
    if lv:
        named = ('<ul class="levels-list compact-only" aria-label="the baselines drawn as levels">'
                 + "".join(f'<li>{svgplot.legend_icon("baseline", banned=d["banned"])}'
                           f'{page.link(d["href"], code(d["name"]))} {esc(combined.fmt(d["m"]["adp"]))} '
                           f'<span class="muted">{"banned operator" if d["banned"] else "not proved"}</span></li>'
                           for d in sorted(lv, key=lambda d: (-d["exact"], d["id"])))
                 + "</ul>")
    return (f'<div class="chart-slot" id="over-time" data-hook="score-chart">'
            f'<figure class="chart-figure"><div class="chart-box" data-score-chart>{variants}</div>{named}'
            + legend_html({d["kind"] for d in es}, front="the best score so far", par=bool(par), levels=bool(lv))
            + f"<figcaption>{score_definition(t)} Dots are the entries by date; the proved references are the "
              "first entries, dated by the commit that last changed their design."
            + (" The dotted levels are baselines: scored, never proved." if lv else "")
            + (f" {len(undated)} undated {'entry is' if len(undated) == 1 else 'entries are'} in the table only."
               if undated else "")
            + "</figcaption></figure>"
            + page.details("every entry by date", page.table(heads("date", "design", "kind", f"score ({combined.UNIT})",
                                                            "area × time"), rows, numeric=(3,)))
            + "</div>")


def nocase(text_html):
    """Units in small-caps text keep their case (uppercase would turn µm² into MM²)."""
    return re.sub(r"µ[^\s),·]*(?:·[^\s),]+)?", lambda m: f'<span class="nocase">{m.group(0)}</span>', text_html)


def heads(*names):
    """Table heads (set in small caps) with their units kept in case: `nocase`."""
    return [page.Html(nocase(esc(n))) if "µ" in n else n for n in names]


def as_of():
    """The date the site is as of: the last commit that changed svGolf (no clock is read), or None
    outside a git checkout."""
    return metrics.commit_date(os.path.join(SVGOLF, "."))


def score_actions(t):
    """The score card's head: the unit, and the linear/log switch (shown by charts.js)."""
    tog = ""
    if entries(t):
        tog = (f'<div class="chart-tools" data-scale-toggle hidden>'
               f'{page.seg(["Linear", "Log"], 0, label_text="scale of the score axis")}</div>')
    return f'<span class="label">area × time · {nocase(esc(combined.UNIT))} · lower is better</span>{tog}'


def explorer_axes(t, ms):
    """The explorer's first pair (x, y): delay (or time) against sky130 area when two designs have
    both, else depth against area in GE."""
    have = lambda a, b: sum(1 for d in t.designs if a in d["m"] and b in d["m"]) >= 2   # noqa: E731
    keys = [m.key for m in ms]
    if "time_ps" in keys and "area_um2" in keys and have("time_ps", "area_um2"):
        return "time_ps", "area_um2"
    return "depth", "area_ge"


def pareto_ids(points):
    """The ids of the proved points (references, records) that no other proved point beats on both
    axes (lower is better; ties kept)."""
    proved = [p for p in points if p["kind"] != "baseline"]
    return sorted(p["id"] for p in proved
                  if not any(q["x"] <= p["x"] and q["y"] <= p["y"] and (q["x"] < p["x"] or q["y"] < p["y"])
                             for q in proved))


def designs_table(t, ms, designs=None):
    """Every design of the page (or `designs`, a measured point's) with all its numbers, by score;
    the metrics `ms` that at least one of them has."""
    designs = t.designs if designs is None else designs
    ms = [m for m in ms if any(m.key in d["m"] for d in designs)]
    rows = []
    for d in sorted(designs, key=score_key):
        tag = {"reference": page.badge("par" if d["par"] else "reference", "par" if d["par"] else "reference"),
               "record": page.badge("submission", "record"),
               "baseline": page.badge("banned operator" if d["banned"] else "not proved",
                                      "banned" if d["banned"] else "baseline")}[d["kind"]]
        name = code(d["name"]) if d["kind"] != "record" else esc(d["name"])
        rows.append(page.Row([(page.link(d["href"], name) if d["href"] else name) + " " + tag]
                             + [esc(m.fmt(d["m"].get(m.key))) if m.key in d["m"] else '<span class="muted">–</span>'
                                for m in ms], cls="par-row" if d["par"] else None))
    return page.table(heads("design", *[m.axis() for m in ms]), rows, numeric=tuple(range(1, len(ms) + 1)),
                      cls="designs")


def scored_view(t):
    return next(v for v in t.views if v["scored"])


def scored_word(t):
    """What the scored point's numbers are: ranked, or for a preview (nothing of it ranked) scored."""
    return "scored" if t.preview else "ranked"


def point_control(t):
    """The explorer's point selector (hidden until charts.js shows it): one button per point, the
    scored one pressed and marked as the ranked one (a preview's: the scored one). "" with one point."""
    if len(t.views) < 2:
        return ""
    scored = ": the scored point, " + ("a preview: not ranked yet" if t.preview else "ranked")
    buttons = "".join(
        f'<button type="button" data-point="{esc(v["key"])}" aria-pressed="{"true" if v["scored"] else "false"}" '
        f'title="{esc(v["full"] + (scored if v["scored"] else ": " + MEASURED))}">'
        f'{esc(v["short"])}{" · " + scored_word(t) if v["scored"] else ""}</button>' for v in t.views)
    return (f'<div class="point-control"><span class="label" id="explore-point-label">Point</span>'
            f'<div class="seg" role="group" aria-labelledby="explore-point-label">{buttons}</div></div>')


def and_list(items):
    items = list(items)
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " and " + items[-1]


def point_note(t):
    """What the explorer is drawn at, said without JavaScript (charts.js rewrites it when another
    point is chosen). "" with one point."""
    if len(t.views) < 2:
        return ""
    v = scored_view(t)
    others = [esc(o["full"]) for o in t.views if not o["scored"]]
    what = ("a preview, so nothing of it is ranked yet" if t.preview else "the ranked numbers")
    return (f'<p class="point-note small" data-point-note><strong>{esc(v["full"])}</strong>, the scored point: '
            f'{what}. The same designs are also measured at {and_list(others)}: <span class="measured">'
            f"{MEASURED}</span>, the same proved "
            f"designs through the same pinned flow at other parameters (the tables below, and "
            f'{page.link("#scaling", "how the designs scale")}).</p>')


def explorer_html(site, t, here):
    """The explorer: two metrics of every design against each other, the Pareto front of the
    proved designs drawn as a step line. The server draws the first pair (`explorer_axes`) at the
    scored point, which is what a reader without JavaScript sees; charts.js shows the point
    selector, the axis menus and the log switches and redraws the chart from the page's data
    (`page_data`): at the scored point the ranked numbers, at any other the measured ones
    (score/measured/<task>.json), labelled measured, not ranked. Under it: every design with all its
    numbers at each point, by score, then the scaling view (`scaling_html`)."""
    ms = task_metrics(t)
    if not t.designs:
        return '<p class="empty">Nothing to compare yet.</p>'
    by = {m.key: m for m in ms}
    xk, yk = explorer_axes(t, ms)
    pts = [{"id": d["id"], "kind": d["kind"], "x": d["m"][xk], "y": d["m"][yk], "banned": d["banned"],
            "tip": tip_lines(d, [by[k] for k in ("adp", xk, yk) if k in by]), "href": d["href"],
            "brief": f"{d['name']} · {kind_text(d)}", "axis_tip": tip_lines(d, [by[xk], by[yk]])[2:],
            "attrs": mark_attrs(d)} for d in t.designs if xk in d["m"] and yk in d["m"]]
    xs = svgplot.Scale(min(p["x"] for p in pts), max(p["x"] for p in pts), 0, 1)
    ys = svgplot.Scale(min(p["y"] for p in pts), max(p["y"] for p in pts), 0, 1)
    svg = "".join(
        f'<div class="chart-variant" data-size="{"compact" if compact else "wide"}">'
        + svgplot.scatter_chart(pts, x_label=by[xk].axis(), y_label=by[yk].axis(), x_log=xs.log, y_log=ys.log,
                                x_integer=xk in metrics.INTEGER, y_integer=yk in metrics.INTEGER,
                                front=pareto_ids(pts), compact=compact,
                                title=f"{t.name}: {by[yk].label.lower()} against {by[xk].label.lower()}")
        + "</div>" for compact in (False, True))
    menu = "".join(f'<option value="{esc(m.key)}">{esc(m.axis())}</option>' for m in ms)

    def axis_control(a, key, log):
        sel = menu.replace(f'value="{esc(key)}"', f'value="{esc(key)}" selected', 1)
        return (f'<div class="axis-control"><label class="label" for="explore-{a}">{a.upper()} axis</label>'
                f'<select id="explore-{a}" data-axis="{a}">{sel}</select>'
                f'<label class="log-toggle"><input type="checkbox" data-log="{a}"{" checked" if log else ""}> log</label>'
                "</div>")
    missing = len(t.designs) - len(pts)
    every = {d["kind"] for v in t.views for d in v["designs"]} | {d["kind"] for d in t.designs}
    banned = any(d["banned"] for v in t.views for d in v["designs"]) or any(d["banned"] for d in t.designs)
    kinds = {k for k in every if k != "baseline" or any(not d["banned"] for v in t.views for d in v["designs"]
                                                         if d["kind"] == "baseline")} | ({"banned"} if banned else set())
    tables = page.details("every design with all its numbers, by score"
                          + (f" (at {esc(scored_view(t)['full'])}, {scored_word(t)})" if len(t.views) > 1 else ""),
                          designs_table(t, ms))
    for v in t.views:
        if not v["scored"]:
            tables += page.details(f"at {esc(v['full'])} ({MEASURED}): every design with all its numbers, by score",
                                   designs_table(t, ms, v["designs"]))
    return (f'<div class="chart-slot" data-hook="explorer">'
            f'<div class="explorer-controls" data-explorer-controls hidden>{point_control(t)}'
            f'{axis_control("x", xk, xs.log)}{axis_control("y", yk, ys.log)}</div>'
            + point_note(t)
            + f'<figure class="chart-figure"><div class="chart-box" data-explorer>{svg}</div>'
            + legend_html(kinds, front="the Pareto front of the proved designs")
            + "<figcaption>Lower is better on both axes. The step line joins the proved designs that no other "
              "proved design beats on both; baselines are shown for scale. Choose any two numbers to find the "
              "best design for your own trade-off. "
              f'<span data-explorer-note>{len(pts)} of {len(t.designs)} designs have both numbers'
              f"{'' if not missing else ' (the rest lack one)'}.</span></figcaption></figure></div>"
            + tables + scaling_html(t)
            + data_script(page_data(t), "task-data"))


def scaling_metrics(t):
    """The metrics the scaling view offers (those its lines have; not the proof's length, which is one
    number for every point), in the explorer's order; the first is drawn by the server."""
    have = {k for ln in t.lines for p in ln["pts"] for k in p["m"]}
    return [m for m in metrics.metric_table(metrics.is_clocked(t.task), metrics.input_drive(t.task))
            if m.key in have and m.key != "proof_lines"]


def scale_ticks(t):
    """The scaling view's x ticks: each point's parameter value, labelled by its name when the
    point has one ('binary16'), else by the value."""
    return [{"x": p["x"], "label": p["label"] or svgplot.tick(p["x"])} for p in t.measured["points"]]


def par_line(t):
    """The scaling line of par (the scored point's best proved reference), or None."""
    if not t.par:
        return None
    return next((ln for ln in t.lines if f"reference/{t.par['stem']}" in ln["ids"]), None)


def line_values(t, ln, m, relative):
    """[(point, value)] of line `ln` for metric `m`: the metric, or with `relative` the metric over
    par's at the same point (points where par has none are left out)."""
    base = {p["key"]: p["m"].get(m.key) for p in par_line(t)["pts"]} if relative else {}
    out = []
    for p in ln["pts"]:
        v = p["m"].get(m.key)
        if v is None:
            continue
        if relative:
            if not base.get(p["key"]):
                continue
            v = v / base[p["key"]]
        out.append((p, v))
    return out


def line_tip(t, ln):
    names = ln["names"]
    what = (f"{len(names)} sizes of one generator: {', '.join(names)}" if ln["family"] else
            f"the same numbers at every point: {', '.join(names)}" if len(names) > 1 else None)
    return [ln["name"], KIND_TEXT[ln["kind"]] + (" · banned operator" if ln["banned"] else "") + " · " + MEASURED] \
        + ([what] if what else [])


def point_tip(t, ln, p, m, rel=None):
    full = next((v["full"] for v in t.views if v["key"] == p["key"]), p["key"])
    return [ln["name"], full + (" · the scored point" if p["key"] == t.point_key else " · " + MEASURED),
            f"{m.label}: {m.fmt(p['m'][m.key])}" + (f" {m.unit}" if m.unit else "")
            + (f" (×{rel:.2f} par)" if rel is not None else "")]


def scaling_chart(t, m, relative, compact):
    """The scaling view's drawing for metric `m` (svgplot.line_chart), absolute or over par's."""
    ticks = scale_ticks(t)
    tick_label = {tk["x"]: tk["label"] for tk in ticks}
    xv = [p["x"] for p in t.measured["points"]]
    chart_lines = []
    for ln in t.lines:
        vals = line_values(t, ln, m, relative)
        if len(vals) >= 2:
            chart_lines.append({"id": ln["id"], "kind": ln["kind"], "banned": ln["banned"], "name": ln["name"],
                                "href": ln["href"], "tip": line_tip(t, ln),
                                "pts": [{"x": p["x"], "y": v, "tip": point_tip(t, ln, p, m, v if relative else None)}
                                        for p, v in vals]})
    y_label = f"{m.label} ÷ par's" if relative else m.axis()
    return svgplot.line_chart(
        chart_lines, x_label=t.measured["scale"]["label"], y_label=y_label, x_ticks=[tk["x"] for tk in ticks],
        x_fmt=lambda v: tick_label.get(v, svgplot.tick(v)), x_log=min(xv) > 0 and max(xv) / min(xv) >= 4,
        y_integer=m.key in metrics.INTEGER and not relative, compact=compact,
        guide={"y": 1, "label": f"par: {t.par['stem']}"} if relative else None,
        title=f"{t.name}: {m.label.lower()}{' over par' if relative else ''} against {t.measured['scale']['label']}, "
              "one line per design")


def scaling_html(t):
    """The scaling view: one metric against the task's scaling parameter (points.json `scale`), a
    line per design (`scaling_lines`). The server draws the first metric (`scaling_metrics`: the
    score when the designs have one) over par's at each point when par is measured at two points or
    more (1 is par; a line under 1 beats par at that size, so a crossing is where a design starts to
    pay off), with a table of every line at every point; charts.js adds the metric menu, the
    relative and log switches, and redraws it. "" for a task measured at one point."""
    if not t.lines:
        return ""
    sm = scaling_metrics(t)
    if not sm:
        return ""
    m = sm[0]
    pl = par_line(t)
    relative = bool(pl) and sum(1 for p in pl["pts"] if m.key in p["m"]) >= 2
    drawn = [ln for ln in t.lines if len(line_values(t, ln, m, relative)) >= 2]
    one = [ln for ln in t.lines if len(line_values(t, ln, m, False)) < 2]
    svg = "".join(f'<div class="chart-variant" data-size="{"compact" if compact else "wide"}">'
                  + scaling_chart(t, m, relative, compact) + "</div>" for compact in (False, True)) if drawn else ""
    menu = "".join(f'<option value="{esc(k.key)}"{" selected" if k.key == m.key else ""}>{esc(k.axis())}</option>'
                   for k in sm)
    xv = [p["x"] for p in t.measured["points"]]
    x_log = min(xv) > 0 and max(xv) / min(xv) >= 4
    controls = (f'<div class="explorer-controls" data-scaling-controls hidden>'
                f'<div class="axis-control"><label class="label" for="scaling-y">Number</label>'
                f'<select id="scaling-y" data-scaling-metric>{menu}</select>'
                + (f'<label class="log-toggle"><input type="checkbox" data-scaling-relative{" checked" if relative else ""}>'
                   f" ÷ par</label>" if pl else "")
                + f'</div><div class="axis-control"><span class="label">Axes</span>'
                f'<label class="log-toggle"><input type="checkbox" data-scaling-log="x"{" checked" if x_log else ""}> '
                f"log {esc(t.measured['scale']['param'] or 'x')}</label>"
                f'<label class="log-toggle"><input type="checkbox" data-scaling-log="y"> log y</label></div></div>')
    kinds = {ln["kind"] for ln in drawn if ln["kind"] != "baseline" or not ln["banned"]} \
        | ({"banned"} if any(ln["banned"] for ln in drawn) else set())
    scored = scored_view(t)
    heads_ = ["design"] + [v["full"] + (f" ({scored_word(t)})" if v["scored"] else "") for v in t.views]
    rows = []
    for ln in t.lines:
        at = {p["key"]: p for p in ln["pts"]}
        name = esc(ln["name"]) if ln["kind"] == "record" else code(ln["name"])
        if len(ln["names"]) > 1:
            name += f' <span class="cell-meta">{esc(", ".join(ln["names"]))}</span>'
        rows.append([(page.link(ln["href"], name) if ln["href"] else name)]
                    + [esc(m.fmt(at[v["key"]]["m"][m.key])) if v["key"] in at and m.key in at[v["key"]]["m"]
                       else '<span class="muted">–</span>' for v in t.views])
    single = (f" Measured at one point only, so not drawn: {and_list([code(ln['name']) for ln in one])} (in the table)."
              if one else "")
    shared = [ln for ln in t.lines if len(ln["names"]) > 1 and not ln["family"]]
    fams = [ln for ln in t.lines if ln["family"]]
    names_note = ((" A name with +1, +2, … stands for that many more designs with the same numbers at every point "
                   "(the table names them)." if shared else "")
                  + (f" {and_list([code(ln['name']) for ln in fams])} {'is a family' if len(fams) == 1 else 'are families'}"
                     " of fixed-size baselines, one file per size, each drawn as one line." if fams else ""))
    how = (f"{esc(m.label)} of each design over par's ({code(t.par['stem'])}) at the same point, against "
           f"{esc(t.measured['scale']['label'])}: 1 is par, and a line under it beats par at that size, so where two "
           "lines cross one design starts to pay off against the other." if relative else
           f"{esc(m.label)} of each design against {esc(t.measured['scale']['label'])}.")
    return (f'<h3 id="scaling">How the designs scale <a class="anchor" href="#scaling" '
            f'aria-label="link to this section">#</a></h3>'
            f'<div class="chart-slot" data-hook="scaling">{controls}'
            f'<figure class="chart-figure"><div class="chart-box" data-scaling>{svg}</div>'
            + legend_html(kinds, par=relative)
            + f"<figcaption><span data-scaling-note>{how}</span> One line per design, lower is better: the same proved "
              f"design at each point, through the same pinned flow. {MEASURED.capitalize()}: "
              + ("this task is a preview, so nothing of it is ranked yet." if t.preview else
                 f"the board ranks at {esc(scored['full'])} only.")
              + f" A dashed line is a baseline (not proved).{names_note}{single}"
              f"{scaling_dropped(t)}"
              "</figcaption></figure></div>"
            + page.details(f"every design at every point: {esc(m.axis())}",
                           page.table(heads(*heads_), rows, numeric=tuple(range(1, len(heads_))), cls="designs")))


def scaling_dropped(t):
    """The (design, point) pairs the measurement dropped, with the reason, as a sentence."""
    out = []
    names = {k: v["full"] for k, v in ((v["key"], v) for v in t.views)}
    for p in t.measured["points"]:
        names.setdefault(p["key"], point_names(t, p)[1])
    for e in t.measured["designs"]:
        for key, why in sorted((e.get("dropped") or {}).items()):
            out.append(f"{code(e['name'])} at {esc(names.get(key, key))} ({esc(why)})")
    return f" Not measured: {'; '.join(out)}." if out else ""


def leaderboard_html(site, t, here):
    """The leaderboard list (the right column of a task page): the players' ranked records by
    combined score (`score_key`; equal scores share a rank), then par. The bar is the score
    against the worst one shown."""
    ranked = sorted((d for d in t.designs if d["kind"] == "record"), key=score_key)
    p = par_design(t)
    shown = [d["exact"] for d in ranked + ([p] if p else []) if d["exact"] is not None]
    worst = max(shown) if shown else None
    ref_hashes = {r["sha256"] for r in t.refs}
    rows, prev, rank = [], None, 0
    for k, d in enumerate(ranked, 1):
        if d["exact"] is None or d["exact"] != prev:
            rank, prev = k, d["exact"]
        tags = []
        if d["sha"] in ref_hashes:
            tags.append(page.badge("reference design", "par"))
        if d.get("light"):
            tags.append(page.badge("light check", "light"))
        rows.append(page.BoardRow(rank, page.link(d["href"], esc(d["name"])),
                                  esc(d["date"]) + (" · " + " ".join(tags) if tags else ""),
                                  combined.fmt(d["m"].get("adp")),
                                  esc(breakdown(d) or f"{lb.fmt_ge(round(d['m']['area_ge'] * 1000))} GE, depth {d['m']['depth']}"),
                                  d["exact"] / worst if worst and d["exact"] is not None else None,
                                  "lead" if rank == 1 and d["exact"] is not None else None))
    if t.par:
        s = t.par["score"]
        name = page.link(f"#ref-{t.par['stem']}", code(t.par["stem"]))
        rows.append(page.BoardRow("", name, f"{page.badge('par', 'par')} proved reference",
                                  combined.fmt(p["m"].get("adp")) if p else "–",
                                  esc((breakdown(p) if p else "") or f"{lb.fmt_ge(s['area_mge'])} GE, depth {s['depth']}"),
                                  p["exact"] / worst if p and worst and p["exact"] is not None else None, "par"))
    if t.par and p and p["exact"] is not None:
        par_text = (f"Par, the bar to beat, is the proved reference {code(t.par['stem'])}: "
                    f"{esc(combined.fmt(p['m']['adp']))} {esc(combined.UNIT)} ({esc(breakdown(p))}).")
    elif t.par:
        par_text = (f"Par is the proved reference {code(t.par['stem'])}; no design of this task has a sky130 "
                    "weighing yet, so there is no score to beat yet.")
    else:
        par_text = "There is no par yet."
    empty = None
    if not ranked:
        empty = f"<p><strong>No submissions yet.</strong> {par_text}</p>"
    elif not (p and p["exact"] is not None and any(d["exact"] is not None and d["exact"] < p["exact"] for d in ranked)):
        empty = f"<p>No submission beats par yet. {par_text}</p>"
    return page.board(rows, empty_html=empty)


def board_table_html(site, t, here):
    """Every ranked record with all its columns, by score, and the records not ranked (under the
    list)."""
    rows = []
    parts = []
    recs = {r["record_hash"]: r for r in t.ranked()}
    for k, d in enumerate(sorted((d for d in t.designs if d["kind"] == "record"), key=score_key), 1):
        r = recs[d["id"]]
        m = d["m"]
        base = f"tasks/{t.name}/records/{d['id']}"
        rows.append(page.Row([
            str(k), esc(r["player"]), esc(r["submitted_at"]), esc(combined.fmt(m.get("adp"))),
            esc(f"{m['area_um2']:.1f}") if "area_um2" in m else "–", esc(str(m.get("time_ps", "–"))),
            esc(lb.fmt_ge(r["area_mge"])), str(r["depth"]), str(r["proof_lines"]), assisted(r),
            record_link(t, here, d["id"]), file_links(here, base, (".sv", ".lean"))],
            cls="frontier-row" if k == 1 else None))
    if rows:
        parts.append(page.details("every column: area, time, proof lines, assisted by, files", page.table(
            heads("#", "player", "date", f"score ({combined.UNIT})", "area (µm²)", "time (ps)", "area (GE)", "depth",
                  "proof lines", "assisted by", "record", "files"), rows, numeric=(0, 3, 4, 5, 6, 7, 8))))
    if t.board["unranked"]:
        muted = '<span class="muted">–</span>'
        urows = [[esc(r["player"]), esc(lb.fmt_um2(r["area_e4um2"])) if r["area_e4um2"] is not None else muted,
                  esc(str(r["time_ps"])) if r["time_ps"] is not None else muted,
                  esc(lb.fmt_ge(r["area_mge"])), str(r["depth"]),
                  record_link(t, here, r["record_hash"]), esc(r["reason"])] for r in t.board["unranked"]]
        parts.append(page.details("not ranked: no sky130 score, or not comparable", (
            "<p>A record ranks on its sky130 area and time, weighed under the pinned flow, the current sky130 "
            "pins and the task's input drive, at the task's scoring point. These are not comparable until they "
            "are checked again.</p>"
            + page.table(heads("player", "area (µm²)", "time (ps)", "area (GE)", "depth", "record", "why"), urows,
                         numeric=(1, 2, 3, 4)))))
    return "\n".join(parts)


def design_of(t, kind, stem):
    return next((d for d in t.designs if d["kind"] == kind and d["stem"] == stem), None)


def vs_par_text(t, d, area_mge):
    """A design against par: on the combined score when both have one; on area in GE when par has
    none (a task without sky130 weighings); else '–'."""
    p = par_design(t)
    if p and p["exact"] is not None:
        if d is None or d["exact"] is None:
            return "–"
        return "±0.0%" if d["exact"] == p["exact"] else f"{(d['exact'] - p['exact']) * 100 / p['exact']:+.1f}%".replace("-", "−")
    return vs_par(area_mge, t.par["score"]["area_mge"]) if t.par and area_mge is not None else "–"


def score_cell(d):
    return esc(combined.fmt(d["m"]["adp"])) if d and "adp" in d["m"] else '<span class="muted">–</span>'


def ge_depth_cell(s):
    """The extra GE columns of a score as one cell: '112.000 · 33' (area in GE, depth in gates)."""
    return f"{esc(lb.fmt_ge(s['area_mge']))}\u00a0·\u00a0{s['depth']}" if s else "–"


def sky_cells(t, d):
    """A design's sky130 area (µm²) and time (ps) cells, the ranked pair (metrics.Metric's format)."""
    by = {m.key: m for m in task_metrics(t)}
    return [esc(by[k].fmt(d["m"][k])) if d and k in d["m"] else '<span class="muted">–</span>'
            for k in ("area_um2", "time_ps")]


def references_html(t, here):
    if not t.refs:
        return "<p>No proved reference yet.</p>"
    rows = []
    for ref in t.refs:
        s = ref["score"]
        d = design_of(t, "reference", ref["stem"])
        tags = page.badge("par", "par") if t.par is ref else ""
        if ref["same_design_as"]:
            tags += " " + page.badge(f"same design as {ref['same_design_as']}", "layer")
        base = f"tasks/{t.name}/reference/{ref['stem']}"
        meta = (f'<span class="cell-meta">tactics: {esc(", ".join(ref["tactics"]))}</span>'
                if ref["tactics"] else "")
        if ref["record_hash"]:
            meta += f'<span class="cell-meta">record: {record_link(t, here, ref["record_hash"])}</span>'
        rows.append(page.Row([
            design_cell(code(ref["stem"]) + " " + tags, md_inline(ref["description"]), meta), score_cell(d),
            *sky_cells(t, d), ge_depth_cell(s),
            ("par" if t.par is ref else esc(vs_par_text(t, d, s["area_mge"]))) if s and t.par else "–",
            str(ref["proof_lines"]), file_links(here, base, (".sv", ".lean"))],
            cls="par-row" if t.par is ref else None, id_=f"ref-{ref['stem']}"))
    return ("<p>Proved and accepted designs that ship with the task, written by the maintainers. They are "
            "the first entries, and <strong>par</strong>, the bar to beat, is the one with the best score "
            f"(area × time, {esc(combined.UNIT)}, from the sky130 area and time; a design without a sky130 "
            "weighing has no score and comes after, by its extra GE columns). A reference that was also recorded "
            "links its record under its name: the record holds that reference's design <em>and</em> proof, "
            "matched by the sha256 of both files.</p>"
            + page.table(heads("design", f"score ({combined.UNIT})", "area (µm²)", "time (ps)", "GE · depth",
                               "vs par", "proof lines", "files"), rows, numeric=(1, 2, 3, 4, 5, 6),
                         cls="designs-list", stack=True))


def design_cell(name_html, what_html, meta_html=""):
    """The first cell of a references or baselines row: the name with its badges, what the design
    is under it, and an optional muted line (the proof's tactics)."""
    what = f'<span class="cell-what">{what_html}</span>' if what_html else ""
    return f'<span class="cell-name">{name_html}</span>{what}{meta_html}'


def baselines_html(t, here):
    if not t.baselines:
        return "<p>No baselines for this task.</p>"
    rows = []
    for b in t.baselines:
        s = b["score"]
        d = design_of(t, "baseline", b["stem"])
        flag = page.badge("banned operator", "banned") if b["banned"] else ""
        if s:
            where = ge_depth_cell(s)
        else:
            where = '<span class="muted">' + (f'scored at {esc(", ".join(b["points"]))} only' if b["points"]
                                              else "not scored") + "</span>"
        rows.append(page.Row([design_cell(code(b["stem"]) + " " + flag, md_inline(b["description"])), score_cell(d),
                              *sky_cells(t, d), where,
                              esc(vs_par_text(t, d, s["area_mge"])) if s and t.par else "–",
                              file_links(here, f"tasks/{t.name}/baselines/{b['stem']}", (".sv",))],
                             id_=f"baseline-{b['stem']}"))
    return ("<p><strong>Not entries.</strong> Designs scored by the pinned flow (with the banlist lifted) but "
            "never accepted: unproved, simulation-only, or using an operator the task bans. They show how much "
            "room there is.</p>"
            + page.table(heads("design", f"score ({combined.UNIT})", "area (µm²)", "time (ps)", "GE · depth",
                               "vs par", "file"), rows, numeric=(1, 2, 3, 4, 5), cls="designs-list", stack=True))


def reject_group(stage, stages):
    """Which group of REJECT_GROUPS a rejection at `stage` belongs to."""
    if stage in PROOF_STAGES:
        return "at-proof"
    if stage in stages and "solution" in stages and stages.index(stage) < stages.index("solution"):
        return "before-proof"
    return "after-proof"


def rejects_html(site, t, here):
    if not t.rejects:
        return "<p>No rejected designs are recorded for this task.</p>"
    groups = {gid: [] for gid, _, _ in REJECT_GROUPS}
    for r in t.rejects:
        groups[reject_group(r["stage"], site.stages)].append(r)
    summary, parts = [], []
    for gid, title, intro in REJECT_GROUPS:
        rs = groups[gid]
        if not rs:
            continue
        by_stage = {}
        for r in rs:
            by_stage[r["stage"]] = by_stage.get(r["stage"], 0) + 1
        stages = ", ".join(f"{code(s)} {n}" for s, n in by_stage.items())
        summary.append(f'<li>{page.link("#reject-" + gid, esc(title))}: {len(rs)} '
                       f'design{"" if len(rs) == 1 else "s"} <span class="muted">(by stage: {stages})</span></li>')
        items = []
        for r in rs:
            stage = page.link(rel_link(here, f"rules.html#stage-{r['stage']}"), code(r["stage"]))
            text = md_inline(r["description"]) if r["description"] else '<span class="muted">(no description yet)</span>'
            src = read_text(r["sv"])
            # a licence's notices (copyright, permission, changes) must stay with the code: an SPDX identifier
            # (the SRT attacks, Apache-2.0 WITH SHL-2.1) or the MIT grant (the sorter's attacks)
            if "SPDX-License-Identifier" in src or "Permission is hereby granted" in src:
                design = page.details("the design, with its licence and provenance notices",
                                      page.code_block(src, "sv"), cls="reveal")
            else:
                design = page.details("the design, with its comments left out",
                                      page.code_block(strip_sv_comments(src), "sv"), cls="reveal")
            items.append(f'<li><p class="reject-head">{code(r["stem"] + ".sv")} '
                         f'<span class="muted">({esc(r["kind"])}, stopped at {stage})</span>: {text}</p>{design}</li>')
        parts.append(f'<h3 id="reject-{gid}">{esc(title)}</h3><p class="muted">{intro}</p>'
                     f'<ul class="rejects">{"".join(items)}</ul>')
    return ("<p>Designs that try to score without meeting the statement (negatives), or that exploit a "
            "place where the proof's reading and the scored netlist could differ (attacks). The checker "
            "stops at the first stage that refuses; each design is listed with that stage.</p>"
            f'<ul class="reject-summary">{"".join(summary)}</ul>' + "".join(parts))


def repo_link(repo_url, repo):
    """The URL of repository path `repo` (see `repo_file`), or None. Inside lean-surfaces,
    `repo_url` is the repository that holds both trees. Standalone, svGolf's files are under
    `repo_url` and lean-surfaces' are not linked (they are the dependency's, at the revision
    lake-manifest.json pins)."""
    if not repo_url:
        return None
    if LAYOUT == "inside":
        return f"{repo_url}/{repo}"
    if repo == "svgolf" or repo.startswith("svgolf/"):
        return f"{repo_url}/blob/HEAD/{repo[len('svgolf/'):]}"
    return None


def submit_html(t, repo_url):
    """How to submit. Without a public repository (`repo_url` null) only the
    local flow is shown; with one, the clone and the pull request."""
    stem = f"my_{t.name.strip('_')}"
    lean = "".join(w.capitalize() for w in stem.split("_")) + ".lean"
    data_dir = f"leaderboard/data/{t.name}/"
    clone = ""
    if repo_url:
        top = posixpath.basename(repo_url.rstrip("/"))
        top = top[:-len(".git")] if top.endswith(".git") else top
        clone = f"git clone {repo_url}\ncd {top}" + ("/svgolf\n" if LAYOUT == "inside" else "\n")
    cmds = (clone + ("" if clone else "cd svgolf\n")
            + f"# 1. admissible, and what does it score? (no proof needed; never accepts)\n"
            f"python3.12 check.py tasks/{t.name} {stem}.sv --unproved\n"
            f"# 2. the real check, with your proof (PROVING.md is the guide)\n"
            f"python3.12 check.py tasks/{t.name} {stem}.sv {lean}\n"
            f"# 3. record it (runs the whole check again: full post-synthesis check, OS sandbox)\n"
            f"python3 leaderboard/leaderboard.py add --task {t.name} --player YOUR_HANDLE \\\n"
            f"    --assisted-by \"TOOL OR MODEL\" --sv {stem}.sv --lean {lean}\n")
    if repo_url:
        intro = "<p>From a clone of the repository:</p>"
        after = (f"<p>Step 3 writes your record's three files (<code>.json</code>, <code>.sv</code> and "
                 f"<code>.lean</code>, named by the record's hash) to <code>{esc(data_dir)}</code>. Then open a "
                 f"pull request against {page.link(repo_url, esc(repo_url))} that adds them; CI re-verifies "
                 "it. There is no submission server: nothing is sent anywhere by these commands.</p>")
    else:
        intro = ("<p><strong>Public submissions open when the svGolf repository is published.</strong> Until "
                 "then, this is the flow on a machine that has the repository: check a solution, then record "
                 "it locally.</p>")
        after = (f"<p>Step 3 writes your record's three files (<code>.json</code>, <code>.sv</code> and "
                 f"<code>.lean</code>, named by the record's hash) to <code>{esc(data_dir)}</code>. Nothing is "
                 "sent anywhere: there is no submission server.</p>")
    sandbox = ("<p><code>leaderboard.py add</code> runs the check with <code>--sandbox require</code>: the "
               "proof's Lean, the extractor, Yosys and Verilator must run inside the operating system's "
               "sandbox (Seatbelt on macOS, bubblewrap on Linux). Where that sandbox is missing or fails its "
               "self-test, the check stops with an infrastructure error and nothing is recorded. On such a "
               "machine, <code>--sandbox auto</code> runs the check without it (and says so on stderr), and "
               "<code>--sandbox off</code> skips it: your proof file then runs with your own privileges, and "
               "the record is for your own use, since an official record is made with the sandbox or not at "
               "all. <code>add</code> also weighs the extra sky130 columns, which need the pinned liberty file "
               "once: <code>python3.12 score/ppa.py --fetch-liberty</code>.</p>")
    return (intro + page.code_block(cmds, "bash", name="shell", term=True) + after
            + page.details("the sandbox, and machines without one", sandbox))


def preview_html(t):
    """A preview's status line: why its submissions are not ranked yet (content/tasks/<t>.json)."""
    return f'<p class="preview-note"><strong>Preview.</strong> {md_inline(t.preview_note)}</p>'


def participate_html(t, here):
    """How to participate, in four steps (zk.golf's list): the details are the sections they link."""
    last = ("Beat the field on the score. Par is the best proved reference: "
            + page.link("#leaderboard", "the leaderboard") + " shows it.")
    if t.preview:
        last = ("Golf the score. This task is a preview: submissions are not ranked yet ("
                + page.link("#leaderboard", "why") + ").")
    return page.steps([
        f"Write a circuit with the task's exact {page.link('#interface', '<strong>interface</strong>')}.",
        f"Prove in Lean 4 that it meets the {page.link('#spec', '<strong>trusted statement</strong>')}; "
        f"the {page.link(rel_link(here, 'proving.html'), 'proving guide')} shows how.",
        f"Check and record it ({page.link('#submit', 'how to submit')}): the checker accepts the pair or says "
        "which stage refused it.",
        last,
    ])


def task_page(site, t):
    here = t.page
    task = t.task
    reserved = ("numbers", "score", "statement", "interface", "spec", "closure", "participate", "leaderboard",
                "over-time", "facts", "files", "explore", "scaling", "references", "baselines", "does-not-count",
                "submit", "props-properties", "props-definitions") + tuple(f"reject-{g}" for g, _, _ in REJECT_GROUPS)
    slugger = md.Slugger(reserved)
    tags = [status_badge(task, t.listing)]
    if t.listing == "tutorial":
        tags.append(page.badge("tutorial", "tutorial"))
    tags.append(page.badge(KIND_SHORT.get(t.kind, t.kind), "plain"))
    tags.append(page.badge(f"scored at {point_text(t.point)}", "plain"))

    def h(i, title, *, own_id=False):
        """A section head of the task card; the anchor names the section (or the head itself)."""
        hid = f' id="{i}"' if own_id else ""
        return (f'<h3{hid}>{esc(title)} <a class="anchor" href="#{i}" '
                f'aria-label="link to this section">#</a></h3>')

    def sec(i, content_html):
        return f'<section id="{i}">{content_html}</section>'

    files = [page.button(rel_link(here, f"tasks/{t.name}/Spec.lean"), "Spec.lean", "quiet sm", download=True)]
    if t.props:
        files.append(page.button(rel_link(here, f"tasks/{t.name}/Properties.lean"), "Properties.lean", "quiet sm",
                                 download=True))
    if t.par:
        base = f"tasks/{t.name}/reference/{t.par['stem']}"
        files += [page.button(rel_link(here, base + ext), f"{t.par['stem']}{ext}", "quiet sm", download=True)
                  for ext in (".sv", ".lean")]
    head = page.page_head(
        crumbs_html=(f'<a href="{rel_link(here, "index.html")}"><span class="back" aria-hidden="true">‹</span>Tasks</a>'
                     f" / {esc(t.name)}"),
        number=t.number, title_html=f'{esc(t.title)} <span class="task-id">{code(t.name)}</span>',
        sub_html=esc(t.subtitle) if t.subtitle else None, tags_html=" ".join(tags),
        aside_html=f'<section id="numbers">{preview_html(t) if t.preview else big_numbers(t)}</section>')
    score = page.card(score_html(site, t, here), tag="section", id_="score", title_html="Score",
                      actions_html=score_actions(t))
    task_card = page.card(
        sec("statement", statement_html(site, t, here, slugger))
        + sec("interface", h("interface", "Interface") + interface_html(site, t))
        + sec("spec", h("spec", "The trusted statement") + spec_html(t, here))
        + h("participate", "How to participate", own_id=True) + participate_html(t, here),
        tag="article", label_html="This task",
        actions_html=page.button(rel_link(here, "proving.html"), "Proving guide", arrow=True))
    submit = page.card(submit_html(t, site.config.get("repo_url")), tag="section", id_="submit",
                       label_html="How to submit")
    if t.preview:
        board = page.card(preview_html(t), tag="section", id_="leaderboard", title_html="Not ranked yet")
    else:
        board = page.card(leaderboard_html(site, t, here) + board_table_html(site, t, here), tag="section",
                          id_="leaderboard", title_html="Leaderboard", flush=True,
                          actions_html='<span class="label">by score</span>',
                          foot_html=(f'<div class="legend-row"><span>score: area × time, {esc(combined.UNIT)}</span>'
                                     '<span class="lg-par">par</span></div>'))
    facts = page.card(facts_html(t), id_="facts", label_html="At a glance")
    downloads = page.card('<div class="btn-row">' + "".join(files) + "</div>"
                          + f'<p class="small muted">Every reference and baseline is under '
                            f'{page.link("#references", "proved references")} and '
                            f'{page.link("#baselines", "baselines")}.</p>',
                          id_="files", label_html="Files")
    explore = page.card(explorer_html(site, t, here), tag="section", id_="explore", title_html="Compare the designs",
                        actions_html='<span class="label">any two numbers · lower is better</span>')
    wide = [page.card(content, tag="section", id_=i, title_html=esc(title), title_id=None)
            for i, title, content in (
                ("references", "Proved references", references_html(t, here)),
                ("baselines", "Baselines", baselines_html(t, here)),
                ("does-not-count", "What does not count", rejects_html(site, t, here)))]
    body = (head + score
            + f'<div class="split"><div class="col">{task_card}{submit}</div>'
              f'<div class="col">{board}{facts}{downloads}</div></div>'
            + explore + "".join(wide))
    site.page(here, f"{t.title} ({t.name})", body, scripts=("charts.js",),
              description=f"svGolf task {t.name}: {t.title}." + (f" {t.subtitle}" if t.subtitle else ""))
    # the files the page offers, byte-identical
    site.copy(f"tasks/{t.name}/Spec.lean", t.spec)
    if t.props:
        properties_source_page(site, t)
    for ref in t.refs:
        site.copy(f"tasks/{t.name}/reference/{ref['stem']}.sv", ref["sv"])
        site.copy(f"tasks/{t.name}/reference/{ref['stem']}.lean", ref["lean"])
    for b in t.baselines:
        site.copy(f"tasks/{t.name}/baselines/{b['stem']}.sv", b["sv"])


def properties_source_page(site, t):
    """tasks/<t>/properties.html: Properties.lean verbatim, an anchor on every line and every
    declaration (the cards' "Open in code" land there), its properties listed; and the file itself."""
    tp = t.props
    here = properties_page(t)
    data = read_bytes(tp.file)
    text = data.decode("utf-8")
    crumbs = (f'<a href="{rel_link(here, "index.html")}"><span class="back" aria-hidden="true">‹</span>Tasks</a>'
              f' / <a href="{rel_link(here, t.page)}">{esc(t.name)}</a> / Properties.lean')
    rows = [[page.link(f"#{p.decl}", code(p.name)), code(p.short), str(p.line),
             page.link(rel_link(here, t.page) + f"#prop-{p.name}", "the card")] for p in tp.properties]
    th = tp.theorem
    rows.append([page.link(f"#{th.decl}", code(th.short)), "the theorem", str(th.line), ""])
    dl_ = page.button(rel_link(here, f"tasks/{t.name}/Properties.lean"), "Properties.lean", "quiet sm", download=True)
    body = (page.page_head(crumbs_html=crumbs, title_html=code("Properties.lean"),
                           sub_html=f"The trusted statement of {code(t.name)} as named properties: proved, not trusted.",
                           aside_html=page.stats([page.Stat("Properties", str(sum(1 for p in tp.properties
                                                                                  if p.kind == "property"))),
                                                  page.Stat("Lines", str(line_count(text)))]))
            + page.card(
                f"<p>Each definition below is one property of the {page.link(rel_link(here, t.page + '#spec'), 'trusted statement')}"
                f" ({page.link(rel_link(here, tp.statement.source), code(tp.statement.short))}). The theorem "
                f"{page.link('#' + th.decl, code(th.short))} proves that the statement holds exactly when they all "
                "do, and Lean's kernel checks it, so this file adds nothing to what is trusted.</p>"
                + page.table(["property", "Lean name", "line", "on the task page"], rows, numeric=(2,))
                + page.dl([("file", code(tp.file)), ("module", code(tp.module)), ("sha256", code(sha256(data)))])
                + page.code_block(text, "lean", src=tp.file, name=tp.file, actions_html=dl_, cls="code source",
                                  body_html=leansrc.anchored_html(text, leansrc.declarations(text)))))
    site.page(here, f"Properties.lean ({t.name})", body,
              description=f"svGolf task {t.name}: the trusted statement as named properties, with the proof that "
                          "they are exactly the statement")
    site.copy(f"tasks/{t.name}/Properties.lean", tp.file)


# ---------------------------------------------------------------------------
# record pages
# ---------------------------------------------------------------------------

def previous_frontier_record(rec, records):
    """The record this one was up against: the best (row_key-first) record
    of the Pareto frontier of the task's records submitted before it."""
    key = (rec["submitted_at"], rec["record_hash"])
    earlier = [r for r in records if (r["submitted_at"], r["record_hash"]) < key]
    front = lb.pareto([row for row in map(lb.row_of, earlier) if lb.has_ranked_columns(row)])
    return next((r for r in earlier if front and r["record_hash"] == front[0]["record_hash"]), None)


def diff_html(old_text, new_text, old_name, new_name):
    lines = list(difflib.unified_diff(old_text.splitlines(keepends=True), new_text.splitlines(keepends=True),
                                      fromfile=old_name, tofile=new_name, n=3))
    if not lines:
        return "<p>The two files are identical.</p>"
    out = []
    for ln in lines:
        text = ln if ln.endswith("\n") else ln + "\n"
        cls = ("diff-head" if ln.startswith(("---", "+++")) else "diff-hunk" if ln.startswith("@@")
               else "diff-add" if ln.startswith("+") else "diff-del" if ln.startswith("-") else None)
        out.append(f'<span class="{cls}">{esc(text)}</span>' if cls else esc(text))
    return f'<pre class="code diff"><code>{"".join(out)}</code></pre>'


def gates_html(score, ge_table):
    gates = score.get("gates") or {}
    rows = sorted(gates.items(), key=lambda kv: (-kv[1], kv[0]))
    bars = [(g, n, f"{lb.fmt_ge(round(ge_table.get(g, 0) * 1000) * n)} GE") for g, n in rows]
    # one cell type is a number, not a chart: the table alone says it
    svg = svgplot.bar_chart(bars, title="gate mix: cells of each type in the scored netlist",
                            unit="cells") if len(bars) > 1 else ""
    trows = [[code(g), str(n), esc(f"{ge_table.get(g, 0):.3f}"), esc(lb.fmt_ge(round(ge_table.get(g, 0) * 1000) * n))]
             for g, n in rows]
    trows.append(["<strong>total</strong>", f"<strong>{score.get('num_gates', sum(gates.values()))}</strong>", "",
                  f"<strong>{esc(lb.fmt_ge(score['area_mge']))}</strong>"])
    figure = (f'<figure class="chart-figure">{svg}<figcaption>Cells by type; area is the count weighted by '
              "the pinned GE table.</figcaption></figure>") if svg else ""
    return (figure + page.table(["cell", "count", "GE each", "GE total"], trows, numeric=(1, 2, 3)))


def record_stats(t, rec, is_ref):
    """A record page's big numbers: the ranked sky130 area (µm²) and time (ps), each against par's, and
    the extra GE columns as a note; a record without sky130 columns has its GE area and depth, and says
    that it is not ranked."""
    sc = rec["score"]
    cols = lb.ranked_columns(rec)
    ge_stat = page.Stat("Area in GE", compact_ge(sc["area_mge"]), unit="GE", note=f"depth {sc['depth']}, extra columns")
    if not cols or not lb.has_ranked_columns(cols):
        return [page.Stat("Score", "–", kind="empty", note="no sky130 columns: not ranked"), ge_stat]
    p = par_design(t)
    pm = p["m"] if p and not is_ref else {}

    def fmt_area(v):
        return f"{v:,.0f}".replace(",", " ") if v >= 10000 else f"{v:.1f}"

    def against(v, par_v, text):
        if par_v is None:
            return None
        pct = "±0.0%" if v == par_v else f"{(v - par_v) * 100 / par_v:+.1f}%".replace("-", "−")
        return f"par {text} ({pct})"
    area, time = cols["area_e4um2"] / 10000, cols["time_ps"]
    clocked = f"{cols['cycles']} × {cols['period_ps']} ps" if cols["cycles"] is not None else None
    return [page.Stat("Area", fmt_area(area), unit="µm²",
                      note=("sky130, a proved reference" if is_ref else
                            against(area, pm.get("area_um2"), f"{fmt_area(pm['area_um2'])} µm²")
                            if "area_um2" in pm else "sky130")),
            page.Stat("Time", str(time), unit="ps",
                      note=clocked or (against(time, pm.get("time_ps"), f"{pm['time_ps']} ps")
                                       if "time_ps" in pm else "the critical-path delay")),
            ge_stat]


def record_page(site, t, rec, ge_table):
    h = rec["record_hash"]
    here = f"tasks/{t.name}/records/{h}.html"
    base = f"tasks/{t.name}/records/{h}"
    data_rel = f"svgolf/leaderboard/data/{t.name}/{h}"
    for ext in (".json", ".sv", ".lean"):
        site.copy(base + ext, data_rel + ext)
    sc, proof, chk, ps = rec["score"], rec["proof"], rec["checker"], rec["postsynth"]
    row = next((r for r in t.ranked() + t.board["unranked"] if r["record_hash"] == h), None)
    is_ref = rec["player"] == site.config["reference_player"]
    ref = t.ref_of_record.get(h)
    status = ""
    if is_ref:
        status = page.badge("reference: par, not an entry", "par")
    elif row in t.board["frontier"]:
        status = page.badge("on the Pareto frontier", "frontier")
    elif row in t.board["unranked"]:
        status = page.badge("not ranked", "draft")
    elif row:
        status = page.badge(f"layer {row['layer']}", "layer")
    nums = record_stats(t, rec, is_ref)
    lead = None
    if is_ref:
        what = (f"the proved reference {code(ref['stem'])}: its design and its proof "
                f"{code(posixpath.basename(ref['lean']))} ({ref['proof_lines']} code lines)"
                + (f". {md_inline(ref['description'])}" if ref["description"] else ".")) if ref else \
            "a design of the maintainers that is not one of the task's proved references."
        lead = (f"<p>Recorded by the maintainers from {what} The record shows that reference passing the "
                "whole checker. It is par, the bar to beat, not a player's entry, and it is not ranked among "
                f"the submissions ({page.link(rel_link(here, t.page + '#references'), 'proved references')}).</p>")
    body = [page.page_head(
        crumbs_html=(f'<a href="{rel_link(here, "index.html")}"><span class="back" aria-hidden="true">‹</span>'
                     f'Tasks</a> / <a href="{rel_link(here, t.page)}">{esc(t.name)}</a> / record'),
        title_html=f"Record {code(h[:12])}", tags_html=status or None, lead_html=lead,
        aside_html=page.stats(nums))]

    def card(i, title_html, content_html):
        return page.card(content_html, tag="section", id_=i, title_html=title_html)
    files = rec["files"]
    body.append(card("record", "The record", page.dl([
        ("task", page.link(rel_link(here, t.page), code(t.name))),
        ("player", esc(rec["player"])),
        ("assisted by", esc("; ".join(rec["assisted_by"])) or "none (an unassisted claim)"),
        ("submitted", esc(rec["submitted_at"])),
        ("notes", esc(rec.get("notes") or "") or '<span class="muted">none</span>'),
        ("scoring point", esc(point_text(sc["scoring_point"]))),
        ("design", f"{code(files['sv']['name'])} sha256 {code(files['sv']['sha256'])}"),
        ("proof", f"{code(files['lean']['name'])} sha256 {code(files['lean']['sha256'])}"
                  + (f": the proof of the reference {code(ref['stem'])} ({code(posixpath.basename(ref['lean']))}, "
                     f"{ref['proof_lines']} code lines)" if is_ref and ref else "")),
        ("canonical text", f"sha256 {code(rec.get('canonical_sha256', ''))}"),
        ("record hash", code(h)),
        ("downloads", " ".join(page.link(rel_link(here, base + ext), code(h[:12] + ext)) for ext in (".sv", ".lean", ".json"))),
    ])))
    body.append(card("gates", "Gate mix", gates_html(sc, ge_table)))
    body.append(card("proof", "The proof", page.dl([
        ("code lines", str(proof.get("lines"))),
        ("build time", esc(f"{proof.get('build_seconds')} s")),
        ("axioms", ", ".join(code(a) for a in proof.get("axioms", []))),
        ("tactics seen", ", ".join(code(x) for x in proof.get("tactics", [])) or "none"),
        ("imports", ", ".join(code(x) for x in proof.get("imports", []))),
    ])))
    flow_rows = [("Yosys", chk.get("yosys")), ("Verilator", chk.get("verilator")), ("Lean toolchain", chk.get("lean_toolchain")),
                 ("svGolf revision", chk.get("svgolf_revision")), ("lean-surfaces revision", chk.get("lean_surfaces_revision")),
                 ("canonicalization script", chk.get("canon_script_sha256")), ("scoring script", chk.get("script_sha256")),
                 ("GE table", chk.get("ge_table_sha256")), ("extractor", chk.get("extractor_sha256")),
                 ("canonical RTLIL", sc.get("rtlil_sha256"))]
    mism = lb.flow_mismatch(lb.flow_of(rec), site.flow)
    flow_note = ("<p>Checked under the pinned flow of this site's boards.</p>" if not mism else
                 f"<p>Checked under another flow ({esc(', '.join(mism))} differ): not ranked.</p>")
    body.append(card("checker", "Checker and flow", flow_note
                + page.dl([(k, code(v) if v else '<span class="muted">not recorded</span>') for k, v in flow_rows])
                + page.details("the checker's files (sha256)", page.table(
                    ["file", "sha256"], [[code(f), code(s)] for f, s in sorted(chk.get("files", {}).items())]))))
    ps_rows = [("mode", esc(lb.record_mode(ps))), ("vectors", esc(ps.get("vectors"))),
               ("mismatches", esc(ps.get("mismatches"))), ("point", esc(ps.get("point", ""))),
               ("seed", code(ps.get("seed", ""))),
               ("salted", "yes (a secret salt: the vectors were not predictable)" if ps.get("salted") else "no")]
    if "full_vectors" in ps:
        ps_rows.insert(2, ("full set", esc(ps["full_vectors"])))
    agreed = ("agreed on every one" if ps.get("mismatches") == 0
              else f"disagreed on {ps.get('mismatches')} (a record the checker accepted should have none)")
    body.append(card("postsynth", "Post-synthesis check",
                f"<p>ls-sv's reading of the design and the scored netlist, simulated on the same vectors, "
                f"{esc(agreed)}. The vectors are a sample of the inputs: a guard against the two tools "
                "disagreeing, not a proof.</p>" + page.dl(ps_rows)))
    if isinstance(rec.get("ppa"), dict) and rec["ppa"].get("available"):
        p = rec["ppa"]
        score = combined.of_record(rec)
        why = lb.unranked_reason(rec, t.task, flow=site.flow, identity=site.ppa_identity, input_drive=t.drive)
        body.append(card("ppa", "sky130 columns (the ranked score)", page.dl(
            ([(f"score ({combined.UNIT})", esc(combined.fmt(combined.um2ns(score))))] if score is not None else [])
            + [(k, esc(p.get(k))) for k in ("area_um2_sky130", "delay_ps_sky130", "unit_depth", "cells_sky130",
                                            "ppa_version") if k in p]
            + [("input drive", code(lb.ppa_input_drive(p) or "none named")),
               ("comparable", esc("yes: the current flow, sky130 pins and input drive" if not why else why))])
            + f'<p class="small">{page.link(rel_link(here, REPRODUCE_PAGE), "Reproduce a score")} re-derives these '
              "numbers from the design with the pinned tools.</p>"))
    verify = (f"# re-run the whole check on this record's files (the cost of the original check)\n"
              f"H={h}\n"
              f"mkdir -p rec/{t.name} && cp \"$H.json\" \"$H.sv\" \"$H.lean\" rec/{t.name}/\n"
              f"python3 leaderboard/leaderboard.py verify --data-dir rec --task {t.name} --full\n")
    body.append(card("verify", "Verify it yourself", "<p>Download the three files, then from "
                "<code>svgolf/</code>:</p>" + page.code_block(verify, "bash", name="shell", term=True)
                + "<p><code>verify --offline</code> checks only the hashes and the arithmetic; plain "
                  "<code>verify</code> also rescores the design (seconds, no Lean).</p>"))
    prev = None if is_ref else previous_frontier_record(rec, t.player_records)
    sv_text = read_text(data_rel + ".sv")
    lean_text = read_text(data_rel + ".lean")
    if is_ref:
        pass                                      # par is not compared with the submissions before it
    elif prev:
        p = f"svgolf/leaderboard/data/{t.name}/{prev['record_hash']}"
        body.append(card("diff", "Against the previous frontier record", f"<p>Compared with "
                    f"{record_link(t, here, prev['record_hash'])} by {esc(prev['player'])}, the best record "
                    "before this one.</p>"
                    + diff_html(read_text(p + ".sv"), sv_text, f"{prev['record_hash'][:12]}.sv", f"{h[:12]}.sv")
                    + page.details("the proofs' diff", diff_html(read_text(p + ".lean"), lean_text,
                                                                 f"{prev['record_hash'][:12]}.lean", f"{h[:12]}.lean"))))
    else:
        body.append(card("diff", "Against the previous frontier record", "<p>None: this is the task's first "
                         "submission.</p>"))
    body.append(card("sources", "The sources",
                f"<h3>{code(files['sv']['name'])}</h3>" + page.code_block(sv_text, "sv", src=data_rel + ".sv")
                + page.details(f"{code(files['lean']['name'])} ({proof.get('lines')} code lines)",
                               page.code_block(lean_text, "lean", src=data_rel + ".lean"))))
    site.page(here, f"{t.name} record {h[:12]}", "\n".join(body),
              description=f"svGolf {t.name}: record {h[:12]} by {rec['player']}")


def trusted_pages(site, tasks):
    mods = sorted({(m, p) for t in tasks for m, p in t.closure if p})
    here = SHARED_TRUSTED_PAGE
    shared = [(m, p) for m, p in mods if is_shared_trusted(m)]
    toolchain = sorted({m for t in tasks for m, p in t.closure if p is None})
    tasks_crumb = f'<a href="{rel_link(here, "index.html")}"><span class="back" aria-hidden="true">‹</span>Tasks</a>'
    body = (page.page_head(
                crumbs_html=f"{tasks_crumb} / trusted base", title_html="The shared trusted base",
                sub_html="The modules every task statement rests on.",
                aside_html=page.stats([page.Stat("Modules", str(len(shared))),
                                       page.Stat("Lines", str(sum(line_count(read_text(p)) for _, p in shared)))]))
            + page.card(
                "<p>Every task statement rests on these modules: the ls-sv semantics of SystemVerilog and svGolf's "
                "statement helpers. A proved submission guarantees what its task's statement says under them. "
                "Each task page lists only the trusted text specific to that task. Any module of the ls-sv library "
                "may be imported by a proof; only the modules below are trusted, since proof helpers are "
                "kernel-checked like any submission. The list is computed from the <code>import</code> lines of the "
                "task statements.</p>"
                + page.table(["module", "role", "file", "lines", "sha256"],
                             [trusted_row(m, p, here) for m, p in shared], numeric=(3,))
                + (f"<p>Also trusted: the Lean toolchain ({', '.join(code(m) for m in toolchain)}).</p>"
                   if toolchain else "")))
    site.page(here, "Shared trusted base", body, description="svGolf: the trusted base every task shares")
    for mod, path in mods:
        here = trusted_page(mod)
        data = read_bytes(path)
        text = data.decode("utf-8")
        users = sorted(t.name for t in tasks if any(m == mod for m, _ in t.closure))
        crumbs = (f'<a href="{rel_link(here, "index.html")}"><span class="back" aria-hidden="true">‹</span>Tasks</a>'
                  f' / <a href="{rel_link(here, SHARED_TRUSTED_PAGE)}">trusted base</a>')
        dl_ = page.button(rel_link(here, f"trusted/{mod}.lean"), f"{mod}.lean", "quiet sm", download=True)
        body = (page.page_head(crumbs_html=crumbs, title_html=code(mod), sub_html=esc(module_role(mod)),
                               aside_html=page.stats([page.Stat("Lines", str(line_count(text)))]))
                + page.card(page.dl([("file", code(path)), ("sha256", code(sha256(data))),
                                     ("statements that rely on it", ", ".join(
                                         page.link(rel_link(here, f"tasks/{u}/index.html#spec"), code(u))
                                         for u in users)),
                                     ("download", page.link(rel_link(here, f"trusted/{mod}.lean"),
                                                            code(f"{mod}.lean")))])
                            + page.code_block(text, "lean", src=path, name=path, actions_html=dl_, cls="code source",
                                              body_html=leansrc.anchored_html(text, leansrc.declarations(text)))))
        site.page(here, mod, body, description=f"svGolf trusted base: {mod}")
        site.copy(f"trusted/{mod}.lean", path)


# ---------------------------------------------------------------------------
# the home page
# ---------------------------------------------------------------------------

def task_card(t, here):
    """A task on the home page (zk.golf's challenge card): number, title, subtitle, par, record and
    how far under par, status. The whole card links to the task."""
    tags = [status_badge(t.task, t.listing)]
    if t.listing == "tutorial":
        tags.append(page.badge("tutorial: start here", "tutorial"))
    return (f'<li class="task-card"><div class="task-card-top"><span class="task-no">{esc(t.number)}</span>'
            f'<span class="label">{esc(KIND_SHORT.get(t.kind, t.kind))} · {code(t.name)}</span></div>'
            f'<h3>{page.link(rel_link(here, t.page), esc(t.title))}</h3>'
            + (f"<p>{esc(t.subtitle)}</p>" if t.subtitle else "")
            + f'<div class="tags">{" ".join(tags)}</div>'
            + (preview_html(t) if t.preview else big_numbers(t, notes=False)) + "</li>")


def home_page(site, tasks):
    here = "index.html"
    src = f"{CONTENT}/home.md"
    text = read_text(src)
    secs = md.split_sections(text)
    lines = text.split("\n")
    if not secs or secs[0][0] != 1:
        raise BuildError(f"{src}: the home page starts with its '# ' title")
    _, title, start, _ = secs[0]
    first_h2 = next((s[2] for s in secs if s[0] == 2), len(lines))
    lead = site.render_md("\n".join(lines[start + 1:first_h2]), source=src, here=here, first_line=start + 2).html
    listed = [t for t in tasks if t.listing == "listed"]
    previews = [t for t in tasks if t.preview]
    tut = [t for t in tasks if t.listing == "tutorial"]
    n_refs = sum(1 for t in tasks for r in t.refs if r["score"])
    n_subs = sum(len(t.player_records) for t in tasks)
    buttons = []
    if tut:
        buttons.append(page.button(rel_link(here, tut[0].page), "Start with the tutorial", "primary", arrow=True))
    buttons += [page.button(rel_link(here, "rules.html"), "Read the rules"),
                page.button(rel_link(here, "proving.html"), "The proving guide", "quiet")]
    head_title = md_inline(title).replace("then golf", '<span class="accent">then golf') + "</span>" \
        if "then golf" in title else md_inline(title)
    hero = (f'<header class="hero"><div><p class="label label-accent">SystemVerilog · Lean 4 · logic synthesis</p>'
            f'<h1>{head_title}</h1><div class="hero-lead">{lead}</div>'
            f'<div class="btn-row">{"".join(buttons)}</div></div>'
            + page.stats([page.Stat("Tasks", str(len(listed) + len(previews))),
                          page.Stat("Proved references", str(n_refs)),
                          page.Stat("Submissions", str(n_subs))])
            + "</header>")
    when = ("see a task's “How to submit”" if site.config.get("repo_url")
            else "public submissions start when the svGolf repository is published")
    intro = ("<strong>Par</strong> is the best proved reference that ships with the task: a design the "
             "maintainers wrote and proved, the bar to beat, never an entry. <strong>Record</strong> is the best "
             "accepted design so far; with no submissions it is par. The score is area × time on the sky130 "
             f"cell library ({esc(combined.UNIT)}), lower is better; “–” marks a task whose designs are not "
             "weighed on sky130 yet. <strong>Open for submissions</strong> means the task's "
             f"statement and checker are final ({when}).")
    if previews:
        intro += (" <strong>Preview</strong> marks a task whose statement is still being revised: its designs "
                  "are shown and measured, and its submissions are not ranked until then.")
    cards = "".join(task_card(t, here) for t in tut + listed + previews)
    parts = [hero,
             f'<div class="section-head" id="tasks"><div><p class="label">The course</p><h2>Tasks</h2></div>'
             f"<p>{intro}</p></div>",
             f'<ul class="task-cards">{cards}</ul>']
    # the rest of home.md: a section that is a numbered list ("The loop") as cards, any other as a card
    slugger = md.Slugger(["tasks"])
    for level, sec_title, s0, s1 in secs:
        if level != 2:
            continue
        body = site.render_md("\n".join(lines[s0 + 1:s1]), source=src, here=here, first_line=s0 + 2).html
        sid = slugger.slug(sec_title)
        head = (f'<div class="section-head"><h2 id="{esc(sid)}">{md_inline(sec_title)} <a class="anchor" '
                f'href="#{esc(sid)}" aria-label="link to this section">#</a></h2></div>')
        if body.lstrip().startswith("<ol>"):
            parts.append(head + body.replace("<ol>", '<ol class="loop">', 1))
        else:
            parts.append(head + page.card(body))
    site.page(here, site.config["site_name"], "\n".join(parts), active="index.html",
              description="svGolf: prove a SystemVerilog circuit correct in Lean, then golf its area and delay.")


# ---------------------------------------------------------------------------
# document pages: rules, proving, about, roadmap, refusals
# ---------------------------------------------------------------------------

def stages_table(refusals):
    rows = [page.Row([code(s["id"]), md_inline(s["what"]), md_inline(s["refuses"])], id_=f"stage-{s['id']}")
            for s in refusals["svgolf"]["stages"]]
    return page.table(["stage", "what it does", "refuses"], rows)


def rules_page(site, refusals):
    here = "rules.html"
    cfg = site.config["pages"]["rules"]
    src = cfg["source"]
    text = site.doc_text(src)
    slugger = md.Slugger(["checker-stages"])
    secs = doc_sections(text, cfg["sections"], site.config.get("omit", {}).get(src, []))
    parts, toc = [], []
    for title, fragment, first in secs:
        r = site.render_md(fragment, source=src, here=here, first_line=first, slugger=slugger)
        parts.append(f"<section>{r.html}</section>")
        toc.append((r.headings[0][2], r.headings[0][1]))
        if title == cfg["stages_after"]:
            parts.append('<section><h2 id="checker-stages">The checker\'s stages <a class="anchor" '
                         'href="#checker-stages" aria-label="link to this section">#</a></h2>'
                         "<p><code>check.py</code> runs the stages in this order and stops at the first that "
                         "refuses; the stage is what a rejection names.</p>" + stages_table(refusals) + "</section>")
            toc.append(("checker-stages", "The checker's stages"))
    body = (page.page_head(title_html="Rules", sub_html=(
                f"From {code(src)} of the repository: the rules, the checker's stages, scoring, the banlist "
                f"and the leaderboard. Everything the checker refuses, and why: "
                f"{page.link('refusals.html', 'Refusals')}. How to get a recorded score again, bit for bit: "
                f"{page.link(REPRODUCE_PAGE, 'Reproduce a score')}."))
            + page.doc("\n".join(parts), toc))
    site.page(here, "Rules", body, active=here, description="svGolf's rules, checker stages, scoring and leaderboard.")


REPRODUCE_PAGE = "reproduce.html"


def reproduce_page(site):
    """reproduce.html: the "Reproduce a score" section of score/PPA.md (config.json `pages.reproduce`),
    rendered as it is: the tools and pinned files with their hashes, the pinned flow step by step, and
    the commands that give a recorded number again, bit for bit."""
    here = REPRODUCE_PAGE
    cfg = site.config["pages"]["reproduce"]
    src = cfg["source"]
    text = site.doc_text(src)
    slugger = md.Slugger([])
    parts = []
    for title, fragment, first in doc_sections(text, cfg["sections"], site.config.get("omit", {}).get(src, [])):
        # the section's own heading is the page's title: render the text under it
        head, _, rest = fragment.partition("\n")
        r = site.render_md(rest, source=src, here=here, first_line=first + 1, slugger=slugger)
        parts.append(f"<section>{r.html}</section>")
    body = (page.page_head(title_html="Reproduce a score", sub_html=(
                f"From {code(src)} of the repository. The ranked score, the sky130 A0′ area and time, is a pure "
                "function of the design's text, the pinned flow, the pins and the task's scoring point and input "
                f"drive; these steps give every recorded number again. Scoring in general: "
                f"{page.link('rules.html#scoring', 'the rules')}."))
            + page.doc("\n".join(parts)))
    site.page(here, "Reproduce a score", body, active="rules.html",
              description=cfg.get("description", "How to reproduce an svGolf score bit for bit."))


def doc_page(site, key, here, title):
    cfg = site.config["pages"][key]
    src = cfg["source"]
    text = omit_sections(site.doc_text(src), site.config.get("omit", {}).get(src, []))
    r = site.render_md(text, source=src, here=here)
    site.page(here, title, doc_body(r, title), active=here, description=cfg.get("description", ""))


def doc_body(r, title):
    """A rendered Markdown document as a document page: its `# ` title in the page head, its
    level-2 headings as the contents beside the text."""
    toc = [(i, t) for level, t, i in r.headings if level == 2]
    html_, head = r.html, esc(title)
    m = re.match(r"\s*<h1\b[^>]*>(.*?)</h1>", html_, re.S)
    if m:
        head = re.sub(r'\s*<a class="anchor"[^>]*>#</a>', "", m.group(1))
        html_ = html_[m.end():]
    return page.page_head(title_html=head) + page.doc(html_, toc)


def content_page(site, name, here, title):
    path = f"{CONTENT}/{name}"
    r = site.render_md(read_text(path), source=path, here=here)
    site.page(here, title, doc_body(r, title), active=here)


ROADMAP_STATUS = (("done", "Done"), ("in-progress", "In progress"), ("planned", "Planned"),
                  ("open", "Open questions"))


def roadmap_page(site):
    here = "roadmap.html"
    path = f"{CONTENT}/roadmap.json"
    data = json.loads(read_text(path))
    resolve = site.resolver(path, here)
    parts = []
    toc = []
    known = {k for k, _ in ROADMAP_STATUS}
    for item in data["items"]:
        if item["status"] not in known:
            raise BuildError(f"{path}: item {item['title']!r}: unknown status {item['status']!r}")
    for status, label in ROADMAP_STATUS:
        items = [i for i in data["items"] if i["status"] == status]
        if not items:
            continue
        parts.append(f'<h2 id="{status}">{esc(label)} <span class="badge badge-{status} badge-count">'
                     f'{len(items)}</span></h2><ul class="roadmap">')
        for i in items:
            parts.append(f'<li><strong>{md_inline(i["title"], resolve)}</strong>'
                         f'<div>{md_inline(i["text"], resolve)}</div></li>')
        parts.append("</ul>")
        toc.append((status, esc(label)))
    body = (page.page_head(title_html="Roadmap", lead_html=site.render_md(data["intro"], source=path, here=here).html)
            + page.doc("\n".join(parts), toc))
    site.page(here, "Roadmap", body, active=here, description="Where svGolf is going.")


def refusal_state(e):
    cat = e["category"]
    out = page.badge(cat, f"cat-{cat}")
    if cat == "later" and e.get("prerequisite"):
        out += " " + md_inline(e["prerequisite"])
    elif cat == "never" and e.get("principle"):
        out += " " + code(e["principle"])
    if e.get("proposed") is True:
        out += ' <span class="muted" title="the classification is a proposal, not yet confirmed">(proposed)</span>'
    sv = e.get("svgolf")
    if sv:
        out += "<br>svGolf: " + page.badge(sv["category"], f"cat-{sv['category']}")
        detail = sv.get("principle") or sv.get("prerequisite")
        if detail:
            out += " " + md_inline(detail)
    return out


def refusals_page(site, refusals):
    here = "refusals.html"
    d, sg = refusals, refusals["svgolf"]
    src = site.config["refusals_json"]

    def render(text):
        return site.render_md(text, source=src, here=here).html
    parts = [render(sg["intro"])]
    toc = [("how-to-read", "How to read this page"), ("pipeline", "The pipeline"), ("policies", "Policies")]
    parts.append('<h2 id="how-to-read">How to read this page</h2><p>Every restriction has one of four states; '
                 "a row marked <em>proposed</em> carries a classification that is not yet confirmed.</p>")
    parts.append(page.table(["state", "meaning"], [[page.badge(k, f"cat-{k}"), md_inline(v)]
                                                   for k, v in d["categories"].items()]))
    parts.append("<p>The <code>never</code> rows rest on these principles:</p>")
    parts.append(page.table(["principle", "statement"], [page.Row([code(p["id"]), md_inline(p["text"])],
                                                                  id_=f"principle-{p['id']}") for p in d["principles"]]))
    parts.append('<h2 id="pipeline">The pipeline: where a refusal can happen</h2>'
                 "<p><code>check.py</code> runs the stages in this order and stops at the first that refuses.</p>"
                 + page.table(["stage", "what it does", "refuses"],
                              [[code(s["id"]), md_inline(s["what"]), md_inline(s["refuses"])] for s in sg["stages"]]))
    parts.append('<h2 id="policies">Policies</h2><ul>' + "".join(f"<li>{md_inline(p)}</li>" for p in sg["policies"]) + "</ul>")
    for g in sg["groups"]:
        rows = [e for e in sg["entries"] if e["group"] == g["id"] and not e.get("aggregate")]
        gid = f"group-{g['id']}"
        toc.append((gid, md_inline(g["title"])))
        parts.append(f'<h2 id="{esc(gid)}">{md_inline(g["title"])}</h2>' + render(g["intro"]))
        if rows:
            parts.append(page.table(["refused", "why", "state"], [
                [f"<strong>{md_inline(e['tag'])}</strong><div class=\"muted small\">e.g. {code(e['trigger'])}</div>",
                 md_inline(e["why"]), refusal_state(e)] for e in rows]))
        if g.get("write_ok"):
            parts.append("<p>What you can write:</p>" + page.code_block(g["write_ok"].rstrip(), "sv"))
        if g.get("refused_example"):
            parts.append("<p>What is refused:</p>" + page.code_block(g["refused_example"].rstrip(), "sv"))
    ranked = sorted((e for e in d["entries"] + sg["entries"] if e["category"] == "later" and e.get("value_rank")),
                    key=lambda e: (e["value_rank"], e["id"]))
    parts.append('<h2 id="ls-sv">Constructs the ls-sv tier refuses, as seen from svGolf</h2>'
                 "<p>The <code>extract</code> and <code>design</code> stages pass on the refusals of the language "
                 "tier (ls-sv). The ones a task is most likely to run into, with what has to exist first:</p>"
                 + page.table(["construct", "why you might want it", "prerequisite"],
                              [[code(e["tag"]), md_inline(e.get("value_note", "")), md_inline(e["prerequisite"])] for e in ranked])
                 + "<p>And what will not be accepted for as long as the tools disagree or the construct is not hardware:</p>"
                 + "<ul>" + "".join(f"<li>{md_inline(x)}</li>" for x in sg["never_summary"]) + "</ul>")
    parts.append('<h2 id="lifting">How a refusal becomes allowed</h2><ul>'
                 + "".join(f"<li>{md_inline(x)}</li>" for x in sg["lifting"]) + "</ul>")
    parts.append('<h2 id="limits">Known limits (not refusals)</h2><ul>'
                 + "".join(f"<li>{md_inline(x)}</li>" for x in sg["limits"]) + "</ul>")
    parts.append('<h2 id="more">Where to read more</h2><p>Paths in the lean-surfaces repository:</p><ul>'
                 + "".join(f"<li>{code(x['path'])}: {md_inline(x['what'])}</li>" for x in sg["links"]) + "</ul>")
    toc += [("ls-sv", "The language tier"), ("lifting", "Lifting a refusal"), ("limits", "Known limits")]
    body = (page.page_head(title_html="What the checker refuses, and what you can write",
                           sub_html=f"Rendered from the refusal register {code(src)} (version {esc(d.get('version'))}).")
            + page.doc("\n".join(parts), toc, wide=True))
    site.page(here, "Refusals", body, active=here, description="Every refusal the svGolf checker makes, and why.")


# ---------------------------------------------------------------------------
# machine-readable outputs
# ---------------------------------------------------------------------------

def task_summary(t):
    best, best_time = t.best()
    par = t.par["score"] if t.par else None
    pm = (par_design(t) or {}).get("m") or {}
    return {"name": t.name, "title": t.title, "subtitle": t.subtitle, "kind": t.kind, "status": t.task.get("status"),
            "listing": t.listing, "ranked": not t.preview, "preview_note": t.preview_note,
            "scoring_point": t.point, "page": t.page, "data": f"data/tasks/{t.name}.json",
            "input_drive": t.drive, "ranked_axes": list(lb.RANKED_AXES),
            "par": None if not par else {"design": t.par["stem"], "area_um2": pm.get("area_um2"),
                                         "time_ps": pm.get("time_ps"), "area_mge": par["area_mge"],
                                         "depth": par["depth"]},
            "best": None if not best else {"record_hash": best["record_hash"], "area_e4um2": best["area_e4um2"],
                                           "time_ps": best["time_ps"], "best_time_ps": best_time,
                                           "area_mge": best["area_mge"], "depth": best["depth"]},
            "records": len(t.records), "submissions": len(t.player_records), "solvers": t.solvers(),
            "score": {k: v for k, v in headline(t).items() if not k.endswith("_design")} | {"unit_ascii": combined.UNIT_ASCII,
                                                                 "definition": "sky130 area (um^2) x time (ns)"}}


def task_data(t, reference_player):
    keep = ("name", "title", "status", "kind", "top", "parameters", "ports", "statement", "banlist", "scoring",
            "allowed_axioms", "time_limit_s")
    return {"schema": SCHEMA, "task": without_comment_keys({k: t.task[k] for k in keep if k in t.task}),
            "display": {"title": t.title, "subtitle": t.subtitle}, "listing": t.listing,
            "ranked": not t.preview, "preview_note": t.preview_note,
            "reference_player": reference_player,
            "board": None if t.preview else t.full_board, "submissions_board": None if t.preview else t.board,
            "references": [{k: r[k] for k in ("stem", "sv", "lean", "sha256", "score", "same_design_as",
                                              "proof_lines", "tactics", "record_hash", "description")}
                           | {"par": t.par is r} for r in t.refs],
            "baselines": [{k: b[k] for k in ("stem", "sv", "banned", "score", "description")} for b in t.baselines],
            "rejected": [{k: r[k] for k in ("kind", "stem", "stage", "sv", "description")} for r in t.rejects],
            "spec": {"file": t.spec, "closure": [{"module": m, "file": p} for m, p in t.closure]},
            "properties": None if not t.props else {
                "file": t.props.file, "theorem": t.props.theorem.decl, "page": properties_page(t),
                "properties": [{"name": p.name, "decl": p.decl, "file": p.file, "line": p.line, "kind": p.kind,
                                "text": p.text} for p in t.props.properties],
                "definitions": [{"name": d.name, "decl": d.decl, "file": d.file, "line": d.line, "text": d.text}
                                for d in t.props.definitions]}}


def llms_txt(site, tasks):
    repo_url = site.config.get("repo_url")
    how = (f"Records are made locally with leaderboard/leaderboard.py (written to leaderboard/data/<task>/) and "
           f"handed in by pull request to {repo_url}." if repo_url else
           "Public submissions open when the svGolf repository is published; until then, records are made "
           "locally with leaderboard/leaderboard.py (written to leaderboard/data/<task>/).")
    lines = ["# svGolf", "",
             "> A competition for SystemVerilog hardware: write a combinational circuit, prove in Lean 4 that it "
             "meets a task's trusted statement, and get scored by a pinned flow. The score is area x time on the "
             "sky130 cell library (um^2 x ns: the cell area times the critical-path delay, or times cycles x the "
             "clock period on a clocked task), lower is better; leaderboard.py ranks the Pareto frontier of that "
             "area (um^2) and time (ps). Area in NAND2 gate equivalents and depth (gates on the longest path) are "
             "extra columns. [Reproduce a score](reproduce.html) says how to get the same numbers.", "",
             f"All paths below are relative to this file. There is no submission server. {how} Par, the bar to "
             f"beat, is a task's best proved reference; the records of {site.config['reference_player']} are the "
             "references, not entries.", "",
             "## Pages", "",
             "- [Tasks and scorecard](index.html)",
             "- [Rules, checker stages, scoring, leaderboard](rules.html)",
             "- [Reproduce a score: the pinned tools, files and commands](reproduce.html)",
             "- [How to prove a task](proving.html)",
             "- [Everything the checker refuses](refusals.html)",
             "- [Roadmap](roadmap.html)",
             "- [About svGolf](about.html)", "",
             "## Tasks", ""]
    for t in tasks:
        s = task_summary(t)
        sc = s["score"]
        par = f"par {s['par']['design']} (no sky130 weighing yet)" if s["par"] else "no par"
        if sc["par"] is not None:
            pp = s["par"]
            par = (f"par {combined.fmt(sc['par']).replace(chr(0x202f), ' ')} {combined.UNIT_ASCII} ({sc['par_name']}: "
                   f"{pp['area_um2']} um^2, {pp['time_ps']} ps), record "
                   f"{combined.fmt(sc['record']).replace(chr(0x202f), ' ')} {combined.UNIT_ASCII}")
        b = s["best"]
        best = (f"best submission {lb.fmt_um2(b['area_e4um2'])} um^2, {b['time_ps']} ps" if b else "no submissions yet")
        statement = (f" The statement as named properties: [{properties_page(t)}]({properties_page(t)})."
                     if t.props else "")
        if t.preview:
            par, best = ("a preview, not ranked (" + t.preview_note[:1].lower() + t.preview_note[1:].rstrip(".") + ")",
                         "no par, no board")
        lines.append(f"- [{t.title}]({t.page}) (`{t.name}`): {t.subtitle} Scored at {point_text(t.point)}; "
                     f"{par}; {best}. Data: [{s['data']}]({s['data']}).{statement}")
    lines += ["", "## Data", "",
              "- [data/site.json](data/site.json): every task's par, best submission and counts",
              "- data/tasks/<task>.json: leaderboard.py's board of every record (`board`), the players' board "
              "(`submissions_board`), references, baselines, rejected designs, the statement's import closure "
              "and its properties (`properties`: each one's Lean declaration, file, line and plain-English text)", ""]
    return "\n".join(lines)


def machine_outputs(site, tasks):
    site.add("data/site.json", json_text({"schema": SCHEMA, "revision": site.revision, "flow": site.flow,
                                          "reference_player": site.config["reference_player"],
                                          "tasks": [task_summary(t) for t in tasks]}))
    for t in tasks:
        site.add(f"data/tasks/{t.name}.json", json_text(task_data(t, site.config["reference_player"])))
    site.add("llms.txt", llms_txt(site, tasks))


# ---------------------------------------------------------------------------
# guards: links and the denylist
# ---------------------------------------------------------------------------

class _Links(html.parser.HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids, self.refs = set(), []

    def handle_starttag(self, tag, attrs):
        for k, v in attrs:
            if k == "id" and v:
                self.ids.add(v)
            if k in ("href", "src") and v is not None:
                self.refs.append(v)


def check_links(files):
    """Every relative href/src of every page names an output file, and every
    #fragment an id on the target page."""
    parsed = {}
    for path, data in files.items():
        if path.endswith(".html"):
            p = _Links()
            p.feed(data.decode("utf-8"))
            parsed[path] = p
    errors = []
    for path, p in sorted(parsed.items()):
        for ref in p.refs:
            if re.match(r"^[a-z][a-z0-9+.-]*:", ref):
                continue
            if ref.startswith("/"):
                errors.append(f"{path}: absolute link {ref!r} (the site must work from any directory)")
                continue
            target, _, frag = ref.partition("#")
            dest = posixpath.normpath(posixpath.join(posixpath.dirname(path), target)) if target else path
            if dest not in files:
                errors.append(f"{path}: link {ref!r}: no such output file {dest}")
            elif frag and (dest not in parsed or frag not in parsed[dest].ids):
                errors.append(f"{path}: link {ref!r}: no id {frag!r} in {dest}")
    return errors


VERBATIM_BLOCK = re.compile(r'<pre\b[^>]*\sdata-src="[^"]*"[^>]*>.*?</pre>', re.S)


def site_text(path, data, copies=(), player_text=()):
    """The site's own text in the output file `path`, or None for a repository
    file offered byte for byte (`copies`). A page loses its `<pre data-src>`
    blocks (each reproduces a repository file, which the tests compare byte for
    byte), and every file loses what players wrote in their records (handle,
    assisted_by, notes: a player may name any tool), in each escaping."""
    if path in copies:
        return None
    text = data.decode("utf-8", errors="replace")
    if path.endswith(".html"):
        text = VERBATIM_BLOCK.sub("", text)
    for s in sorted(player_text, key=lambda x: (-len(x), x)):
        if s:
            for form in sorted({s, esc(s), json.dumps(s, ensure_ascii=False)[1:-1]}):
                text = text.replace(form, "")
    return text


def check_denylist(files, denylist, *, copies=(), player_text=()):
    """The output against config.json's `denylist`, case-insensitively. A plain
    string must occur nowhere, repository files offered byte for byte included.
    An object `{"text": ..., "scope": "site-text", "allow": {page: reason}}` is
    an internal marker (a person's name, a work-package code, a review round):
    it must not occur in the site's own text (`site_text`) of any file but the
    pages its `allow` names, and each of those must still contain it (else the
    allowance is stale)."""
    hits = []
    plain, markers = [], []
    for e in denylist:
        if isinstance(e, str):
            plain.append(e)
        elif isinstance(e, dict) and e.get("scope") == "site-text" and e.get("text"):
            markers.append(e)
        else:
            raise BuildError(f"config.json denylist: {e!r} is neither a string nor "
                             '{"text": ..., "scope": "site-text"}')
    for path, data in sorted(files.items()):
        text = data.decode("utf-8", errors="replace").lower()
        hits += [f"{path}: contains the denylisted {w!r}" for w in plain if w.lower() in text]
        own = site_text(path, data, copies, player_text) if markers else None
        if own is None:
            continue
        own = own.lower()
        for m in markers:
            found = m["text"].lower() in own
            if found and path not in m.get("allow", {}):
                hits.append(f"{path}: contains the internal marker {m['text']!r} (denylist, scope site-text)")
            elif not found and path in m.get("allow", {}):
                hits.append(f"{path}: config.json allows the internal marker {m['text']!r} here, but it no longer "
                            "occurs: drop the allowance")
    for m in markers:
        for path in sorted(set(m.get("allow", {})) - set(files)):
            hits.append(f"config.json allows the internal marker {m['text']!r} on {path}, which is not in the output")
    return hits


# ---------------------------------------------------------------------------
# the build
# ---------------------------------------------------------------------------

def load_config():
    with open(os.path.join(SITE, "config.json"), encoding="utf-8") as fh:
        return json.load(fh)


def load_denylist(path):
    """Extra denylist entries (config.json's format: a JSON list) from a file kept outside the
    repository, for the markers a public configuration must not spell out."""
    try:
        with open(path, encoding="utf-8") as fh:
            extra = json.load(fh)
    except (OSError, ValueError) as e:
        raise BuildError(f"--denylist {path}: {e}")
    if not isinstance(extra, list):
        raise BuildError(f"--denylist {path}: not a JSON list")
    return extra


def build_site(*, offline=False, strict=False, revision=None, config=None, denylist=()):
    """Build the whole site in memory. Returns the Site (its `files` are the
    output tree). Raises BuildError. `denylist`: entries added to config.json's."""
    config = dict(config or load_config())
    config["denylist"] = list(config.get("denylist") or []) + list(denylist)
    site = Site(config, strict=strict, revision=revision)
    refusals = json.loads(site.doc_text(site.config["refusals_json"]))
    site.stages = [s["id"] for s in refusals["svgolf"]["stages"]]
    tasks = collect(site, offline)
    ge_table = json.loads(read_text("svgolf/score/ge.json"))
    site.add("style.css", read_bytes("svgolf/site/style.css"))
    site.add("site.js", read_bytes("svgolf/site/site.js"))
    site.add("charts.js", read_bytes("svgolf/site/charts.js"))
    home_page(site, tasks)
    for t in tasks:
        task_page(site, t)
        for rec in t.records:
            record_page(site, t, rec, ge_table)
    trusted_pages(site, tasks)
    rules_page(site, refusals)
    reproduce_page(site)
    doc_page(site, "proving", "proving.html", "Proving")
    refusals_page(site, refusals)
    roadmap_page(site)
    content_page(site, "about.md", "about.html", "About")
    machine_outputs(site, tasks)
    errors = check_links(site.files) + check_denylist(site.files, site.config["denylist"], copies=site.copies,
                                                      player_text=site.player_text)
    if strict:
        errors += [f"warning (fatal under --strict): {w}" for w in site.warnings]
    if errors:
        raise BuildError("\n".join(errors))
    return site


def write_tree(files, out):
    """Replace the directory `out` with `files`. A non-empty directory is
    replaced only if an earlier build marked it."""
    if os.path.exists(out):
        if not os.path.isdir(out):
            raise BuildError(f"{out} exists and is not a directory")
        if os.listdir(out) and not os.path.isfile(os.path.join(out, MARKER)):
            raise BuildError(f"{out} is not empty and was not written by this script ({MARKER} is missing): "
                             "refusing to replace it")
        shutil.rmtree(out)
    for path, data in sorted(files.items()):
        dest = os.path.join(out, *path.split("/"))
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        with open(dest, "wb") as fh:
            fh.write(data)
    with open(os.path.join(out, MARKER), "w", encoding="utf-8") as fh:
        fh.write("Written by svgolf/site/build.py; replaced on every build.\n")


def main(argv=None):
    ap = argparse.ArgumentParser(description="Build the svGolf static site (nothing is deployed).")
    ap.add_argument("--out", default=OUT_DEFAULT, help="output directory (default: site/_out, git-ignored)")
    ap.add_argument("--offline", action="store_true",
                    help="skip the check that this machine's Yosys flow matches the pin in tests/expected.json")
    ap.add_argument("--strict", action="store_true", help="make every warning fatal")
    ap.add_argument("--revision", help="a revision label for the footer and data/site.json (e.g. a git hash)")
    ap.add_argument("--denylist", metavar="FILE",
                    help="a JSON list of denylist entries added to config.json's (kept outside the repository)")
    args = ap.parse_args(argv)
    if args.revision is not None and not re.fullmatch(r"[A-Za-z0-9._+-]{1,64}", args.revision):
        ap.error("--revision: 1 to 64 characters of letters, digits and . _ + -")
    try:
        extra = load_denylist(args.denylist) if args.denylist else ()
        site = build_site(offline=args.offline, strict=args.strict, revision=args.revision, denylist=extra)
        write_tree(site.files, args.out)
    except (BuildError, md.MarkdownError) as e:
        print(f"site build FAILED:\n{e}", file=sys.stderr)
        return 1
    for w in site.warnings:
        print(f"warning: {w}", file=sys.stderr)
    pages = sum(1 for p in site.files if p.endswith(".html"))
    print(f"site: {len(site.files)} files ({pages} pages) in {os.path.relpath(args.out)}; "
          f"{len(site.unlinked)} repository paths "
          + ("linked to the repository" if site.config.get("repo_url") else
             "shown unlinked (no public repository URL yet)"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
