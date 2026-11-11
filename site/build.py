#!/usr/bin/env python3
"""svGolf's static site generator.

    python3.12 site/build.py [--out DIR] [--offline] [--strict] [--revision REV] [--denylist FILE]

Run from svgolf/ (any directory works; paths are taken from this file). Any
Python 3.9 or later, standard library only. It writes the whole site to
`site/_out/` (git-ignored) or to `--out`:

  index.html                      what svGolf is, a card per task (par, record), the loop
  tasks/<t>/index.html            a listed task: par, record and how far under par on the score
                                  (area x time on sky130: leaderboard/combined.py); the score card
                                  (the score of each entry over time; its caption the one definition of
                                  the score and of par, record and under par; its last line a link to
                                  how to submit); then two columns: the task (statement,
                                  interface, the trusted statement as a panel of property cards, the
                                  definitions they use (props.py) and what does not count, with
                                  Spec.lean and its trusted import closure, how to participate), how to
                                  submit (the path of a first submission: the two files, the copy of par's
                                  pair, the four commands, what "done" is, the Lean file, the record)
                                  beside the leaderboard (by score); under the two columns, start a new
                                  design (the README's card: the route of a design of your own); the
                                  designs compared (any two numbers
                                  against each other, with the Pareto front, at the scored point or,
                                  measured, not ranked, at any other point of score/points.json; and
                                  how the designs scale: one number against the task's parameter, a
                                  line per design); the proved references
                                  (par), the baselines; the files it offers
                                  (Spec.lean, Properties.lean, reference/, baselines/) next to it,
                                  byte-identical
  tasks/<t>/properties.html       the task's Properties.lean verbatim, an anchor per line and per
                                  declaration (where a property card's "Open in code" lands)
  tasks/<t>/records/<hash>.html   one page per record, with its .json, .sv and .lean (byte-identical): the
                                  overview (Area, Performance and Score cards, with "beats / matches" over
                                  the task's other players' ranked records once there are any: standing.py);
                                  the sources across the page (the code first); then two columns: the
                                  netlist card, whose tabs are the schematic of a small display instance,
                                  the critical path node by node and the cells (the committed data of
                                  site/schematics/, written by site/gen_schematics.py), and under it the
                                  checker and a combinational record's post-synthesis check; beside them the
                                  record and the proof; then a clocked record's post-synthesis check, the
                                  design among the task's designs on an area-time plot, the diff against the
                                  previous frontier record, reproduce and verify
  tasks/<t>/reference/<stem>.html the same page for a proved reference that has no record (a preview's
                                  references have none: they are rows of its task page)
  trusted/<module>.html           every module of the statements' trusted import closure, verbatim,
                                  an anchor per line and per declaration (leansrc.py)
  rules.html refusals.html proving.html roadmap.html about.html
  reproduce.html                  score/PPA.md's "Reproduce a score": the pinned tools, files and commands
  llms.txt llms-full.txt          what an agent reads: the commands, the Lean contract, the tasks; the
                                  proving guide in plain text
  data/site.json data/tasks/<t>.json style.css site.js charts.js pdk.js

Every golf score is shown on sky130, the default, or on ASAP7 (decided 2026-11-09: the library selector, on the home page
and in every page's header; `dual`, `both`): a page carries both views, ranked here at build time from the records'
sky130 columns and from leaderboard/asap7/<task>.json, and pdk.js (loaded first, in the head) shows the reader's choice,
kept in the URL (?pdk=asap7) and, where the browser allows it, in its storage. Without JavaScript: sky130.

The look is style.css's design system (a pixel golf course), page.py's components and pixelart.py's
drawings (inline SVG, decorative: the home page's hero art and icons, the logo, the flag at the
end of a page head's rule); every page reads without JavaScript (site.js adds the copy buttons
of code blocks and the property panel's tabs; pdk.js the library selector). A task page's charts are drawn here as SVG
(svgplot.py; the numbers come from metrics.py) and its data is embedded as inert JSON; charts.js
adds the score chart's linear/log switch, tooltips, the explorer's point selector and axis menus,
and the scaling view's metric menu and switches.

Inputs, all from the repository: tasks/<t>/ (task.json, README.md, Spec.lean,
reference/, and properties.json + Properties.lean: the statement as named
properties, the Lean text of each cut from its file by declaration name),
tests/expected.json (scores, baselines, attacks, negatives and the
pinned flow), score/measured/<t>.json (the designs measured at every
point of score/points.json by score/points.py), site/schematics/ (each page's schematic and
critical-path data, generated by site/gen_schematics.py and only read here: no Yosys, no Node), the
records under leaderboard/data/ and the ASAP7 view's columns under leaderboard/asap7/ (read and ranked by
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
`config.json`'s `reference_player` are the proved references' (the best of them
is par, the bar to beat): they are shown with the proved references, never
ranked among the players.

How to submit: until `config.json` names the public repository (`repo_url`),
a task page says that public submissions open when it is published and shows
the local flow only; with a `repo_url`, it shows the clone and the pull request.

Boards are built under the flow pinned in tests/expected.json, so the output
is a function of the repository alone: a task's board under the pin of its
kind's flow (decided 2026-11-07: `flow`, svgolf.ys and ge.json, for a
combinational task; `flow_seq`, svgolf_seq.ys and ge_seq.json, for a clocked
one; leaderboard.py's `task_flow`). Unless `--offline`, the build first
checks that the machine's flows (leaderboard.py's `current_flow(svgolf, flow)`:
the Yosys version and the hashes of canon.ys and of the flow's script and GE
table) match those pins on every key; a missing Yosys counts as a mismatch. Deterministic: no clock is
read, iteration is sorted, areas stay integer milli-GE until printed, and
chart coordinates are rounded to 0.1, so two builds are byte-identical.

Guards, each fatal: every relative link and anchor of the output resolves;
no `config.json` denylist entry occurs in it (a plain string anywhere, an
internal marker in the site's own text: see `check_denylist`); a stale
redaction (its text no longer in the source) fails; an unsupported Markdown
construct fails with file:line. `--denylist FILE` adds entries (a JSON list in config.json's format)
kept outside the repository. `--strict` makes the warnings fatal too (today:
a task with no `content/tasks/<t>.md`, whose README intro is used instead, a
task that `config.json` does not list, a missing or stale curated text in
`content/tasks/<t>.json` or `content/attacks/<t>.json`, and a design the ASAP7
view would show without a bound entry in `leaderboard/asap7/<t>.json`).

Exit status: 0 built, 1 a guard or check failed, 2 usage error.
"""

import argparse
import contextlib
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
import pixelart                                   # noqa: E402
import props                                      # noqa: E402
import standing                                   # noqa: E402
import svgplot                                    # noqa: E402
from metrics import combined                      # noqa: E402  (leaderboard/combined.py: the score)
from highlight import highlight, language_of, tokens   # noqa: E402
from page import esc, code                        # noqa: E402

OUT_DEFAULT = os.path.join(SITE, "_out")
CONTENT = "svgolf/site/content"                   # the site's own texts (a repository path: `repo_file`)
MARKER = ".svgolf-site"                           # marks a directory this script may replace
SCHEMA = "svgolf-site/1"
TOOLCHAIN_ROOTS = ("Init", "Std", "Lean", "Lake")
KIND_SHORT = {"comb-family": "parametric", "comb-fixed": "fixed size", "react-family": "clocked, reactive",
              "tx-family": "clocked, transaction", "stream-family": "clocked, stream"}
# THE LIBRARY SELECTOR (decided 2026-11-09: a dropdown on the front page lets the reader see the golf scores on sky130
# or on ASAP7). Every golf score the site shows (the boards and their order, par and the record, the
# ranks, the score and Pareto charts, a task page's score card, a detail page's overview) is built twice here: on sky130,
# the default and the records' own columns, and on ASAP7, the derived columns of leaderboard/asap7/<task>.json; both
# ranked by leaderboard.py's own functions at build time (`asap7_state`). A page carries both, each in an element of
# class `pdk-sky130` or `pdk-asap7` (`dual`, `both`), and style.css shows the one <html data-pdk> names: pdk.js sets it
# from the URL's ?pdk= (a shared link), else the reader's stored choice, before the page is drawn, and the selector
# (on the home page and in every page's header) changes it, the stored choice and the URL. Without JavaScript the
# page shows sky130 and says the ASAP7 view needs the selector. Nothing else on the site changes with it.
PDK_NAME = {"sky130": "sky130", "asap7": "ASAP7"}
PDK_A = {"sky130": "a sky130", "asap7": "an ASAP7"}       # the name with its article ("an ASAP7 weighing")
ASAP7_ANCHOR = "the-asap7-view"            # README.md's "### The ASAP7 view": how it is scored, its quirks (rules.html)
VIEW_ATTRS = ("pdk", "designs", "board", "full_board", "par", "views", "lines")
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


_ID_ATTR = re.compile(r'(?<![\w-])id="([^"]+)"')
_ID_REF = re.compile(r'(?<![\w-])(href|for|aria-labelledby|aria-describedby|aria-controls)="([^"]*)"')


def suffix_ids(html_, suffix):
    """`html_` with every id it defines suffixed (and the references to them inside it: in-page links, `for`, the
    aria relations), so that a second copy of a fragment (the ASAP7 view's, `both`) keeps the page's ids unique.
    A link to an id the fragment does not define is left alone."""
    ids = set(_ID_ATTR.findall(html_))
    if not ids:
        return html_
    out = _ID_ATTR.sub(lambda m: f'id="{m.group(1)}{suffix}"', html_)

    def ref(m):
        attr, val = m.group(1), m.group(2)
        if attr == "href":
            return f'href="#{val[1:]}{suffix}"' if val.startswith("#") and val[1:] in ids else m.group(0)
        return f'{attr}="' + " ".join(v + suffix if v in ids else v for v in val.split()) + '"'
    return _ID_REF.sub(ref, out)


def dual(sky_html, a7_html, *, inline=False):
    """The two views of one piece of a page (the library selector): the sky130 one first, then the ASAP7 one, each in
    an element of class `pdk-<library>` (`span`s for `inline` text); style.css shows the chosen one."""
    tag = "span" if inline else "div"
    return f'<{tag} class="pdk pdk-sky130">{sky_html}</{tag}><{tag} class="pdk pdk-asap7">{a7_html}</{tag}>'


def both(t, fn, *, inline=False):
    """`fn()` drawn in both views of task `t` (`Task.view`), the ASAP7 copy's ids suffixed (`suffix_ids`): `dual`."""
    sky = fn()
    with t.view("asap7"):
        a7 = suffix_ids(fn(), "-asap7")
    return dual(sky, a7, inline=inline)


def pdk_text(sky_html, a7_html):
    """Inline text that names the library: `dual` of two spans."""
    return dual(sky_html, a7_html, inline=True)


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
        self.flow = None                          # the pinned combinational flow (tests/expected.json `flow`)
        self.flows = {}                           # flow name -> its pin (`flow`, `flow_seq`): `flow_for`
        self.ppa_identity = None                  # the sky130 identity they are built under (lb.ppa_identity)
        self.a7_identity = None                   # the ASAP7 view's (lb.asap7_identity)
        self.stages = []                          # the checker's stages, in order (the refusal register)
        self._sky = None

    def warn(self, msg):
        self.warnings.append(msg)

    def flow_for(self, task):
        """The pinned flow of `task`'s kind (leaderboard.py `task_flow`): the one its records are compared with."""
        pin = self.flows.get(lb.task_flow(task))
        if pin is None:
            raise BuildError(f"{task['name']}: a {task.get('kind')} task's records are compared with the clocked "
                             "flow, and tests/expected.json has no `flow_seq` pin for it")
        return pin

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

    def page(self, path, title, body_html, *, active=None, description="", scripts=(), scores=False):
        """A page; `scores`: it shows golf scores, so in the ASAP7 view a banner at its top says so (`asap7_banner`)."""
        self.add(path, page.layout(title=title, body_html=body_html, root=root_of(path), active=active,
                                   description=description, revision=self.revision,
                                   site_name=self.config["site_name"], scripts=scripts,
                                   banner_html=asap7_banner(path) if scores else ""))

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
        self.flow = None                            # the pin of the task's kind's flow (`Site.flow_for`)
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
        self.pdk = "sky130"                       # the library the attributes of VIEW_ATTRS are of now (`view`)
        self.states = {}                          # pdk -> {VIEW_ATTRS: values}: sky130's, and ASAP7's (`asap7_state`)
        self.a7_table = None                      # leaderboard/asap7/<task>.json (lb.load_asap7), or None

    @property
    def preview(self):
        """A preview: listed, its designs shown and measured, nothing ranked (no par, no record, no board)."""
        return self.listing == "preview"

    @property
    def kind(self):
        return self.task.get("kind", "")

    @contextlib.contextmanager
    def view(self, pdk):
        """The task as the ASAP7 (or sky130) view shows it: VIEW_ATTRS (its designs, boards, par, the explorer's
        points and the scaling lines) swapped for that library's while the block runs, so that every renderer draws
        that library's numbers through the same code."""
        saved = {k: getattr(self, k) for k in VIEW_ATTRS}
        for k, v in self.states[pdk].items():
            setattr(self, k, v)
        try:
            yield self
        finally:
            for k, v in saved.items():
                setattr(self, k, v)

    def ranked(self):
        """The players' ranked records (the reference player's are par, not entries)."""
        return self.board["frontier"] + self.board["dominated"]

    def best(self):
        """(the players' best record, the first row of their board's ranking by area × time; the fastest time among
        their ranked records), or (None, None). Not the frontier's first row: that is the smallest area, which is the
        best score only while the frontier has one record."""
        ranking = self.board["ranking"]
        if not ranking:
            return None, None
        return ranking[0], min(r["time_ps"] for r in ranking)

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
    # ranked by area x time (the boards' `ranking`; `frontier`/`dominated` are the Pareto layers, for exploring),
    # under the pinned flow, the repository's sky130 identity (score/ppa_pins.json) and the task's input drive:
    # leaderboard.py's own comparability rule
    t.drive = lb.ppa_setup_now(task).get("input_drive")
    t.flow = site.flow_for(task)                   # the pin of the task's kind's flow
    # the task's trusted statement as the repository has it: a record checked under another one (or made before
    # records named theirs) is not ranked (leaderboard.py `statement_mismatch`, decided 2026-11-07)
    t.statement = lb.current_statement_or_none(task, SVGOLF)
    t.board = lb.build_board(task, t.player_records, flow=t.flow, identity=site.ppa_identity, input_drive=t.drive,
                             statement=t.statement)
    t.full_board = lb.build_board(task, t.records, flow=t.flow, identity=site.ppa_identity, input_drive=t.drive,
                                  statement=t.statement)
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
    t.measured = metrics.load_measured(name, site.ppa_identity, t.drive, warn=site.warn)
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
    t.views, t.lines = point_views(t), scaling_lines(t)
    t.states["sky130"] = {k: getattr(t, k) for k in VIEW_ATTRS}
    t.states["asap7"] = asap7_state(site, t, expected)
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

    def as_flow(pin):
        return {"yosys": pin["yosys_version"], "canon_script_sha256": pin["canon_script_sha256"],
                "script_sha256": pin["script_sha256"], "ge_table_sha256": pin["ge_table_sha256"]}
    # the pin of each flow: a task's records are compared with its kind's (`Site.flow_for`, decided 2026-11-07)
    site.flow = as_flow(expected["flow"])
    site.flows = {lb.COMB_FLOW: site.flow}
    if expected.get("flow_seq"):
        site.flows[lb.SEQ_FLOW] = as_flow(expected["flow_seq"])
    site.ppa_identity = lb.ppa_identity()          # score/ppa_pins.json: a repository file, no liberty needed
    site.a7_identity = lb.asap7_identity()          # score/ppa_pins_asap7.json: likewise
    if not offline:
        for name, want in site.flows.items():
            now = lb.current_flow(SVGOLF, name)
            bad = sorted(k for k, v in want.items() if now.get(k) is None or now[k] != v)
            if bad:
                raise BuildError(f"the machine's {'clocked ' if name == lb.SEQ_FLOW else ''}scoring flow differs from "
                                 f"the pin in tests/expected.json{' (`flow_seq`)' if name == lb.SEQ_FLOW else ''} on "
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


def measured_at_scored(t, ref):
    """A reference's sky130 columns at the scoring point from score/measured/<task>.json (score/points.py: the same
    pinned flow, equal to the goldens bit for bit where both exist, score/test_points.py), in Sky130's form; or None.
    For a reference with neither a golden nor a comparable record of its own."""
    if not t.measured:
        return None
    e = next((e for e in t.measured["designs"] if e["kind"] == "reference" and e["name"] == ref["stem"]
              and e["sha256"] == ref["sha256"]), None)
    r = (e or {}).get("at", {}).get(t.point_key)
    if not r or r.get("time_ps") is None:
        return None
    return {"area_e4um2": r["area_e4um2"], "delay_ps": r["time_ps"], "cells": r.get("cells"), "area_mge": r["area_mge"],
            "depth": r["depth"]}


REFERENCE_DATES = f"{CONTENT}/reference_dates.json"   # when each reference joined its task (gen_reference_dates.py)


def reference_date(t, ref, rec):
    """When a proved reference joined its task (UTC, to the second): `REFERENCE_DATES`, which keeps
    the dates a fresh-history copy of the repository no longer has; else the date of the last commit
    that changed its design, else its own record's submission date."""
    if not hasattr(reference_date, "table"):
        try:
            reference_date.table = json.loads(read_text(REFERENCE_DATES))
        except FileNotFoundError:
            reference_date.table = {}
    return (reference_date.table.get(t.name, {}).get(ref["stem"]) or metrics.commit_date(repo_file(ref["sv"]))
            or (rec or {}).get("submitted_at"))


def task_designs(site, t):
    """Every design the task page compares, one dict each: the proved references, the players'
    ranked records and the baselines that have a score at the scoring point. Keys: id (unique on
    the page), kind (reference | record | baseline), stem (a reference's or baseline's name), name,
    sha (of the design file), date (a record's submission date; a reference's is when it joined its
    task, `reference_date`; a baseline has none), href (where
    its mark links: a record's page, a reference's or baseline's row on the page), banned, layer (a
    record's Pareto layer of (sky130 area, time), an exploration column), m (its metrics, `metrics.design_metrics`: the sky130
    columns of its golden, else of its own comparable record, else for a reference its measured numbers at the scoring
    point, `measured_at_scored`) and
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
            rec, t.task, flow=t.flow, identity=site.ppa_identity, input_drive=t.drive, statement=t.statement)
               else None)
        if gold is None and own is None:
            gold = measured_at_scored(t, ref)
        m, exact = metrics.design_metrics(s, sky=gold, ppa=own,
                                          energy=sky.energy_of(t.name, ref["stem"], t.point_key),
                                          proof_lines=ref["proof_lines"])
        out.append({"id": f"reference/{ref['stem']}", "kind": "reference", "stem": ref["stem"], "name": ref["stem"],
                    "sha": ref["sha256"], "date": reference_date(t, ref, rec),
                    "href": rel_link(t.page, reference_page(t, ref)), "banned": False, "m": m, "exact": exact,
                    "par": False, "player": None})
    for r in t.ranked():
        rec = next(x for x in t.player_records if x["record_hash"] == r["record_hash"])
        m, exact = metrics.design_metrics(rec["score"], ppa=rec.get("ppa"), proof_lines=r["proof_lines"],
                                          sky=sky.of_rtlil(t.name, t.point, rec["score"].get("rtlil_sha256")))
        out.append({"id": r["record_hash"], "kind": "record", "stem": None, "name": r["player"],
                    "sha": rec["files"]["sv"]["sha256"], "date": r["submitted_at"], "layer": r["layer"],
                    "href": f"records/{r['record_hash']}.html", "banned": False, "m": m, "exact": exact,
                    "par": False, "light": r.get("postsynth") == "light", "player": r["player"]})
    for b in t.baselines:
        if not b["score"]:
            continue
        m, exact = metrics.design_metrics(b["score"], sky=sky.of_file(t.name, t.point, repo_file(b["sv"])),
                                          energy=sky.energy_of(t.name, b["stem"], t.point_key))
        out.append({"id": f"baseline/{b['stem']}", "kind": "baseline", "stem": b["stem"], "name": b["stem"],
                    "sha": sha256(read_bytes(b["sv"])), "date": None, "href": f"#baseline-{b['stem']}",
                    "banned": b["banned"], "m": m, "exact": exact, "par": False, "player": None})
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


LIBRARY_FREE = ("area_ge", "depth", "gates", "ffs", "proof_lines")   # a design's numbers that no library changes


def asap7_metrics(m0, e):
    """A design's metrics in the ASAP7 view, and its exact ASAP7 score (1e-5 µm² × ps), or None: the numbers no library
    changes (LIBRARY_FREE) from `m0`, its sky130 metrics, and the area, time (and a clocked design's period and cycles)
    of `e`, its entry in leaderboard/asap7/<task>.json (None: no ASAP7 numbers). The energy figures are sky130's and
    stay out."""
    m = {k: m0[k] for k in LIBRARY_FREE if k in m0}
    if e is None:
        return m, None
    exact = combined.exact(e["area_e5um2"], e["time_ps"])
    m.update(area_um2=e["area_e5um2"] / 100000, time_ps=e["time_ps"])
    if e["cycles"] is not None:
        m.update(period_ps=e["delay_ps"], cycles=e["cycles"])
    m["adp"] = combined.um2ns(exact, "asap7")
    return m, exact


def asap7_state(site, t, expected):
    """The task as the ASAP7 view shows it (VIEW_ATTRS; `Task.view`), computed from the repository at build time like
    sky130's: the boards are leaderboard.py's (`build_board` on the ASAP7 columns, bound to each record by
    `asap7_columns`), the designs are `task_designs`' with their ASAP7 numbers (a reference's and a baseline's entry
    found by its file's sha256 and checked against its GE columns and cycles), par is the proved reference with the
    best ASAP7 score under the same tie rule as sky130's, and the explorer has the scored point only (ASAP7 is weighed
    there alone: no scaling lines). A gap in the view (`asap7_gaps`) is a warning, fatal under --strict."""
    table = t.a7_table = lb.load_asap7(t.name, warn=site.warn)
    stale = None if table is None else lb.asap7_table_mismatch(table, t.task, identity=site.a7_identity, flow=t.flow)
    if stale:
        site.warn(f"{t.name}: leaderboard/asap7/{t.name}.json: {stale}: the ASAP7 view shows no numbers for this task "
                  "(`leaderboard.py asap7 --write`)")
    asap7_gaps(site, t, table, expected)
    kw = dict(flow=t.flow, statement=t.statement, pdk="asap7", asap7=table, asap7_identity=site.a7_identity)
    board = lb.build_board(t.task, t.player_records, **kw)
    full_board = lb.build_board(t.task, t.records, **kw)
    sky = {d["id"]: d for d in t.designs}

    def entry(sha, s, what):
        e = None if (table is None or stale) else lb.asap7_entry(table, sha)
        if e is not None and (e["area_mge"], e["depth"], e["cycles"]) != (s["area_mge"], s["depth"], s.get("cycles")):
            site.warn(f"{t.name}: the ASAP7 entry of {what} is not bound to its GE columns and cycles at the scoring "
                      "point: not shown")
            return None
        return e
    out = []
    for ref in t.refs:
        d = sky.get(f"reference/{ref['stem']}")
        if d is None:
            continue
        m, exact = asap7_metrics(d["m"], entry(ref["sha256"], ref["score"], f"the reference {ref['stem']}"))
        out.append(dict(d, m=m, exact=exact, par=False))
    recs = {r["record_hash"]: r for r in t.player_records}
    for r in board["frontier"] + board["dominated"]:
        rec = recs[r["record_hash"]]
        m0, _ = metrics.design_metrics(rec["score"], proof_lines=r["proof_lines"])
        m, exact = asap7_metrics(m0, lb.asap7_entry(table, rec["files"]["sv"]["sha256"]))
        out.append({"id": r["record_hash"], "kind": "record", "stem": None, "name": r["player"],
                    "sha": rec["files"]["sv"]["sha256"], "date": r["submitted_at"], "layer": r["layer"],
                    "href": f"records/{r['record_hash']}.html", "banned": False, "m": m, "exact": exact,
                    "par": False, "light": r.get("postsynth") == "light", "player": r["player"]})
    for b in t.baselines:
        d = sky.get(f"baseline/{b['stem']}")
        if d is None:
            continue
        m, exact = asap7_metrics(d["m"], entry(d["sha"], b["score"], f"the baseline {b['stem']}"))
        out.append(dict(d, m=m, exact=exact, par=False))
    exact = {d["stem"]: d["exact"] for d in out if d["kind"] == "reference"}
    scored = [(k, r) for k, r in enumerate(t.refs) if r["row"] and r["stem"] in exact]
    par = None
    if scored and not t.preview:                 # a preview has no par in either view
        par = min(scored, key=lambda kr: (exact[kr[1]["stem"]] is None, exact[kr[1]["stem"]] or 0,
                                          kr[1]["row"]["area_mge"], kr[1]["row"]["depth"], kr[0]))[1]
    for d in out:
        d["par"] = bool(par) and d["kind"] == "reference" and d["stem"] == par["stem"]
    view = {"key": t.point_key, "short": point_text(t.point), "full": point_text(t.point), "x": None, "scored": True,
            "designs": out}
    return {"pdk": "asap7", "designs": out, "board": board, "full_board": full_board, "par": par, "views": [view],
            "lines": []}


def asap7_gaps(site, t, table, expected):
    """A design the task's pages show at the scoring point (a record, the reference player's too, a proved reference
    or a baseline with a score there) without a bound entry in leaderboard/asap7/<task>.json, or an entry for a design
    the task no longer has: a warning, fatal under --strict, so that a publish build never ships a partial ASAP7 view
    (the view itself then says "not ranked" or "–", and never shows a sky130 number in its place). The check is
    `leaderboard.py asap7`'s own (`asap7_designs`, `asap7_check`, offline); a new or re-seeded record needs
    `leaderboard.py asap7 --write`."""
    designs = lb.asap7_designs(t.task, t.records, expected)
    if not designs:
        return
    where = f"leaderboard/asap7/{t.name}.json"
    if table is None:
        if not os.path.isfile(lb.asap7_path(t.name, lb.ASAP7_DIR)):   # a file there but bad: load_asap7 said why
            site.warn(f"{t.name}: no {where}: the ASAP7 view shows no numbers for this task "
                      "(`leaderboard.py asap7 --write` measures them)")
        return
    fails, _notes = lb.asap7_check(t.task, table, designs, identity=site.a7_identity, flow=t.flow)
    for f in fails:
        site.warn(f"{t.name}: {where}: {f}: the ASAP7 view is partial (`leaderboard.py asap7 --write`)")


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
        ref = refs.get(e["name"])
        href = rel_link(t.page, reference_page(t, ref)) if ref else f"#ref-{e['name']}"
        proof = (ref or {}).get("proof_lines")
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
    count as the first entries, so with no submission the record is par, and an entry that only ties
    par's score leaves the record at par, named so); UNDER how far the record
    is below par, as a fraction. All None when par has no sky130 weighing."""
    p = par_design(t)
    es = entries(t)
    if p is None or p["exact"] is None or not es:
        return {"par": None, "record": None, "under": None, "unit": combined.UNIT, "par_name": None,
                "record_name": None, "par_design": None, "record_design": None}
    best = min(es, key=lambda d: (d["exact"], d["date"] or "~", d["id"]))
    if best["exact"] == p["exact"]:
        best = p                                  # a tie with par is no record: the Record shows par itself
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
        """The design's name and its ranked factors, area × time ('add_n · 460.4 µm² × 2.59 ns'; a latency kind's
        time with its factors named, 'matmul_g1 · 87 174 µm² × 4 cycles × 10.7 ns period')."""
        return f"{name} · {breakdown(d, t, labels=True)}" if d and breakdown(d, t) else name
    return page.stats([
        page.Stat("Par", combined.fmt(h["par"]), unit=h["unit"], note=note(h["par_name"], h["par_design"]) if notes else None),
        page.Stat("Record", combined.fmt(h["record"]), unit=h["unit"],
                  note=note(h["record_name"], h["record_design"]) if notes else None),
        page.Stat("Under par", under_text(h["under"]), kind="accent" if h["under"] and h["under"] > 0 else None)])


def ns(ps, pdk="sky130"):
    """Picoseconds as nanoseconds with three significant digits: '2.60', '10.7', '378'; on ASAP7 (`pdk`), whose times
    are mostly under a nanosecond, '0.563'."""
    v = ps / 1000
    if pdk == "asap7" and v < 1:
        return f"{v:.3f}"
    return f"{v:.2f}" if v < 10 else f"{v:.1f}" if v < 100 else f"{v:.0f}"


def area_short(um2, pdk="sky130"):
    """An area in µm² for a score's factors: '460.4', '87 174' (thin-space groups from 10 000); on ASAP7 (`pdk`),
    whose areas are about 65 times smaller, three decimals as in the ASAP7 tables: '6.998', '131.204'."""
    if um2 >= 10000:
        return f"{um2:,.0f}".replace(",", "\u202f")
    return f"{um2:.3f}" if pdk == "asap7" else f"{um2:.1f}"


def breakdown(d, t=None, *, labels=False):
    """A score's factors as text: '460.4 µm² × 2.60 ns', a clocked one '87 174 µm² × 4 × 10.7 ns'; a design of
    a reactive task `t` (one decision per cycle, no latency) '769.5 µm² × 2.83 ns', its time being the period.
    `labels` names a latency kind's two time factors, '... µm² × 4 cycles × 10.7 ns period' (the page head's big
    numbers). In the ASAP7 view (`t.pdk`) the same with ASAP7's sizes: '6.998 µm² × 0.563 ns'."""
    m = d["m"]
    if "area_um2" not in m or "time_ps" not in m:
        return ""
    pdk = getattr(t, "pdk", "sky130")
    area = area_short(m["area_um2"], pdk)
    if "cycles" in m and "period_ps" in m and (t is None or metrics.has_latency(t.task)):
        if labels:
            return f"{area} µm² × {counted(m['cycles'], 'cycle')} × {ns(m['period_ps'], pdk)} ns period"
        return f"{area} µm² × {m['cycles']} × {ns(m['period_ps'], pdk)} ns"
    return f"{area} µm² × {ns(m['time_ps'], pdk)} ns"


# A task's curated text (content/tasks/<t>.md) never types a measured number: it writes a placeholder,
# `{{DESIGN.FIELD}}`, and the build fills it from the same data the page's tables show. DESIGN is a
# proved reference's or a baseline's stem, or `par`; FIELD is `area` ('460.4 µm²'), `time` ('2.61 ns'),
# `score` ('1202 µm²·ns'), `ge` ('112 GE') or `depth` ('33'). A number typed next to a unit (µm², ns, ps,
# GE) is a warning, fatal under --strict: it would go stale the next time the flow or a design changes.
PLACEHOLDER = re.compile(r"\{\{\s*([A-Za-z0-9_]+)\.([a-z]+)\s*\}\}")
HAND_TYPED = re.compile(r"(?<![\w.{])\d[\d., ]*\s?(?:µm²|um\^2|ns|ps|GE)(?![\w²^])")
PLACEHOLDER_FIELDS = ("area", "time", "score", "ge", "depth")
LIBRARY_FIELDS = ("area", "time", "score")      # the fields that are sky130's numbers (GE and depth: either library's)


def area_text(um2):
    """An area in µm² as the page writes it: '460.4', '12 357' (thin-space groups from 10 000)."""
    return f"{um2:,.0f}".replace(",", " ") if um2 >= 10000 else f"{um2:.1f}"


def placeholder_metrics(t, stem):
    """The metrics a placeholder reads: the design's on the task page (a reference first, then a
    baseline), the sky130 columns completed from score/measured/<task>.json at the scoring point (the
    same pinned flow, equal to the goldens where both exist) for a design with no golden."""
    if stem == "par":
        d = par_design(t)
    else:
        d = next((d for kind in ("reference", "baseline") for d in t.designs
                  if d["kind"] == kind and d["stem"] == stem), None)
    if d is None:
        return None
    m = dict(d["m"])
    if ("area_um2" not in m or "time_ps" not in m) and t.measured:
        e = next((e for e in t.measured["designs"] if e["kind"] == d["kind"] and e["name"] == d["stem"]
                  and e["sha256"] == d["sha"]), None)
        r = (e or {}).get("at", {}).get(t.point_key) or {}
        if r.get("area_um2") is not None and r.get("time_ps") is not None:
            m.update(area_um2=r["area_um2"], time_ps=r["time_ps"],
                     adp=combined.um2ns(combined.of_columns(area_um2=r["area_um2"], time=r["time_ps"])))
    return m


def fill_placeholders(site, t, text, source):
    """`text` (content/tasks/<t>.md) with its `{{DESIGN.FIELD}}` placeholders filled (PLACEHOLDER); an
    unknown design or field, or one the data has no number for, fails the build. A hand-typed number
    with a unit is a warning (HAND_TYPED)."""
    for i, line in enumerate(text.split("\n"), 1):
        for m in HAND_TYPED.finditer(PLACEHOLDER.sub("", line)):
            site.warn(f"{source}:{i}: the hand-typed number {m.group(0)!r}: write a placeholder "
                      "({{DESIGN.area}}, {{DESIGN.time}}, ...) so that the build fills it from the data")

    def fill(m):
        stem, field = m.group(1), m.group(2)
        if field not in PLACEHOLDER_FIELDS:
            raise BuildError(f"{source}: {m.group(0)}: the field is one of {', '.join(PLACEHOLDER_FIELDS)}")
        ms = placeholder_metrics(t, stem)
        if ms is None:
            raise BuildError(f"{source}: {m.group(0)}: task {t.name} has no reference or baseline {stem!r}")
        key = {"area": "area_um2", "time": "time_ps", "score": "adp", "ge": "area_ge", "depth": "depth"}[field]
        v = ms.get(key)
        if v is None:
            raise BuildError(f"{source}: {m.group(0)}: no {key} for {stem} at the scoring point")
        if field == "area":
            return f"{area_text(v)} µm²"
        if field == "time":
            return f"{ns(v)} ns"
        if field == "score":
            return f"{combined.fmt(v)} {combined.UNIT}"
        if field == "ge":
            return lb.fmt_ge(round(v * 1000)).rstrip("0").rstrip(".") + " GE"
        return str(v)
    return PLACEHOLDER.sub(fill, text)


def check_headline(t, d):
    """The last stderr line `check.py` prints for design `d` of task `t` (check.py's `ranked_headline`, the same
    format): its sky130 area and time, area x time, and par as the page shows it."""
    m, p = d["m"], par_design(t)
    if d.get("exact") is None or "area_um2" not in m or "time_ps" not in m:
        raise BuildError(f"{t.name}: {d['name']} has no sky130 weighing: no ranked line")
    line = (f"ranked (sky130 A0'): {m['area_um2']} um^2 x {m['time_ps']} ps = "
            f"{combined.um2ns(d['exact']):.2f} {combined.UNIT_ASCII}")
    if p is None or p["exact"] is None:
        return line + "; par: none recorded"
    return line + f"; par {combined.um2ns(p['exact']):.2f} ({p['name']})"


# home.md types no measured number either: `{{TASK/DESIGN.FIELD}}` is a task's placeholder (FIELD as above), or
# `{{TASK/DESIGN.headline}}`, the last line check.py prints for that design (`check_headline`), or, alone on its
# line, `{{TASK/DESIGN.sv}}`, the design's source without its comments (`strip_sv_comments`), indented as the line.
HOME_PLACEHOLDER = re.compile(r"\{\{\s*([A-Za-z0-9_]+)/([A-Za-z0-9_]+)\.([a-z]+)\s*\}\}")


def fill_home(site, tasks, text, source):
    """home.md with its `{{TASK/DESIGN.FIELD}}` placeholders filled (HOME_PLACEHOLDER); an unknown task, design
    or field fails the build, a hand-typed number with a unit is a warning (fatal under --strict)."""
    by_name = {t.name: t for t in tasks}
    for i, line in enumerate(text.split("\n"), 1):
        for m in HAND_TYPED.finditer(HOME_PLACEHOLDER.sub("", line)):
            site.warn(f"{source}:{i}: the hand-typed number {m.group(0)!r}: write a placeholder "
                      "({{add/add_n.area}}, {{add/add_n.headline}}, ...) so that the build fills it from the data")

    def design(m):
        t = by_name.get(m.group(1))
        if t is None:
            raise BuildError(f"{source}: {m.group(0)}: no listed task {m.group(1)!r}")
        d = next((d for d in t.designs if d["kind"] in ("reference", "baseline") and d["stem"] == m.group(2)), None)
        if d is None and m.group(2) == "par":
            d = par_design(t)
        if d is None:
            raise BuildError(f"{source}: {m.group(0)}: task {t.name} has no reference or baseline {m.group(2)!r}")
        return t, d

    out = []
    for line in text.split("\n"):
        whole = HOME_PLACEHOLDER.fullmatch(line.strip())
        if whole and whole.group(3) == "sv":
            t, d = design(whole)
            path = next(x["sv"] for x in (t.refs if d["kind"] == "reference" else t.baselines) if x["stem"] == d["stem"])
            indent = line[:len(line) - len(line.lstrip())]
            out += [indent + ln if ln else ln for ln in strip_sv_comments(read_text(path)).rstrip("\n").split("\n")]
            continue

        def fill(m):
            t, d = design(m)
            if m.group(3) == "headline":
                return check_headline(t, d)
            if m.group(3) == "sv":
                raise BuildError(f"{source}: {m.group(0)}: a design's source stands alone on its line")
            return fill_placeholders(site, t, "{{" + d["stem"] + "." + m.group(3) + "}}", source)
        out.append(HOME_PLACEHOLDER.sub(fill, line))
    return "\n".join(out)


ORDER_COMPARISONS = ("<", "<=", ">", ">=")


def bans_order_comparisons(ops):
    """score/banlist.py's bans_order_comparisons (decided 2026-11-05): a task that bans `+` or `-` bans the run-time
    ordering comparisons too (Yosys builds each as its own adder)."""
    return bool(set(ops) & {"+", "-"})


def banned_operators(task):
    """Every run-time operator task `task` bans: its banlist's, and the ordering comparisons when they go with it."""
    ops = list(task.get("banlist", {}).get("operators", []))
    return ops + (list(ORDER_COMPARISONS) if bans_order_comparisons(ops) else [])


def statement_html(site, t, here, slugger):
    """The task section's text, content/tasks/<t>.md: the one statement of the task on its page (what to build, the
    range, the bans, the clocking rules). The build checks that it names every banned operator in a code span
    (2026-11-09: the add, mul and clmul texts had left out the ordering comparisons)."""
    path = f"{CONTENT}/tasks/{t.name}.md"
    if os.path.isfile(repo_file(path)):
        raw = read_text(path)
        spans = [s.split() for s in re.findall(r"`([^`]+)`", raw)]
        named = {tok for s in spans if all(re.fullmatch(r"[^\w\s]+", x) for x in s) for tok in s}   # operator lists
        missing = [o for o in banned_operators(t.task) if o not in named]
        if missing:
            site.warn(f"{path}: the task text does not name the banned run-time operator"
                      f"{'s' if len(missing) > 1 else ''} {' '.join(missing)} (in a code span); it is the page's one "
                      "statement of the bans")
        text = fill_placeholders(site, t, raw, path)
        # the text quotes sky130's numbers (area, time, score; GE and depth are the same on either library) and
        # compares designs by them: the ASAP7 view says so above it, as it does on the netlist card
        quotes = any(m.group(2) in LIBRARY_FIELDS for m in PLACEHOLDER.finditer(raw))
        note = ('<p class="pdk-asap7 pdk-note small">This text quotes sky130 numbers and compares the designs on '
                "sky130, the default library; the score, the boards and the charts of this page are on ASAP7, where "
                "the order of the designs can differ.</p>") if quotes else ""
        return note + site.render_md(text, source=path, here=here, slugger=slugger, heading_shift=1).html
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


def solution_wall_factor():
    """check.py's SOLUTION_WALL_FACTOR (the solution compile's wall-clock backstop, in multiples of the task's CPU
    limit), read from its text: the site never imports the checker."""
    m = re.search(r"^SOLUTION_WALL_FACTOR = (\d+)$", read_text("svgolf/check.py"), re.M)
    if not m:
        raise BuildError("svgolf/check.py has no `SOLUTION_WALL_FACTOR = <n>` line")
    return int(m.group(1))


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
    if bans_order_comparisons(ops):
        banned += (", and the run-time ordering comparisons " + " ".join(code(o) for o in ORDER_COMPARISONS)
                   + " (Yosys builds each as its own adder, an " + code("$alu") + "; equality stays allowed)")
    comment = t.banlist_note or task.get("banlist", {}).get("_comment")
    facts.append(("banned run-time operators", banned + (f'<p class="muted">{md_inline(comment)}</p>' if comment else "")))
    facts.append(("allowed axioms", ", ".join(code(a) for a in task.get("allowed_axioms", []))))
    # the limit counts CPU seconds (decided 2026-11-05); check.py's SOLUTION_WALL_FACTOR gives the wall-clock backstop
    limit = task.get("time_limit_s")
    facts.append(("proof time limit", esc(f"{limit} s of CPU time (a wall-clock backstop of "
                                          f"{solution_wall_factor() * limit:g} s stops a proof that waits)")
                  if isinstance(limit, (int, float)) else esc(f"{limit}")))
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


def properties_html(site, t, here):
    """The property panel (props.py): one card per property a circuit must have (a plain-English
    paragraph, its Lean text cut from Properties.lean, its file and a link into the source view),
    the definitions they use, and the theorem that makes the cards exactly the trusted statement.
    A task without a properties.json gets one card, the statement as a whole (its own prose and
    declaration, from Spec.lean). The last tab is "What does not count" (2026-11-09; before, a card at the
    bottom of the page): the designs the checker rejects, next to the properties they break."""
    rejects = ("does-not-count", "What does not count", len(t.rejects),
               f'<div class="props-text">{rejects_html(site, t, here)}</div>')
    if t.props:
        return props.panel(t.props, task_dir=t.dir, proved=None, rejected=0, extra_panes=[rejects], title_tag="h4",
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
    return page.props_panel([("props-properties", "Properties", 1, card), rejects], hook="properties", title_tag="h4")


def spec_html(site, t, here):
    spec_text = read_text(t.spec)
    spec_link = page.link(rel_link(here, f"tasks/{t.name}/Spec.lean"), code("Spec.lean"))
    split = (" Below it is split into the properties a circuit must have, one card each: what the property "
             "guarantees in plain words, and its exact Lean text. Every proved reference has all of them."
             if t.props else " The proved references meet it.")
    parts = [f"<p>A proof must establish the task's trusted statement, the constant "
             f"{code(t.task['statement']['constant'])} of {spec_link} (module {code(t.task['statement']['module'])})."
             f"{split} The last tab, {page.link('#does-not-count', 'what does not count')}, lists the designs the "
             "checker rejects.</p>",
             properties_html(site, t, here),
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
    return [m for m in metric_table(t) if m.key in have]


def metric_table(t):
    """metrics.metric_table for the task: a reactive task's time is the period (no latency column). In the view
    `t.pdk` (the ASAP7 view: its columns, its input drive)."""
    clocked = metrics.is_clocked(t.task)
    pdk = getattr(t, "pdk", "sky130")
    drive = metrics.asap7_input_drive() if pdk == "asap7" else metrics.input_drive(t.task)
    return metrics.metric_table(clocked, drive, latency=not clocked or metrics.has_latency(t.task), pdk=pdk)


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


RATING_BUILD = "svgolf/score/reference_build.json"
RATING_BUILD_ANCHOR = "rating-build"


def rating_build():
    """The build the ranked numbers are rated with (decided 2026-11-05), from data: score/reference_build.json (the
    Yosys and yosys-abc binaries and the determinism measurements), the liberty's sha256 from score/ppa_pins.json,
    and the sha256 of score/ppa.py, score/ppa_pins.json and the flow scripts computed from the files themselves."""
    rb = json.loads(read_text(RATING_BUILD))
    pins = json.loads(read_text("svgolf/score/ppa_pins.json"))
    return {"yosys": rb["yosys"], "abc": rb["abc"], "determinism": rb["determinism"], "decided": rb["decided"],
            "liberty": {"file": pins["liberty"]["file"], "sha256": pins["liberty"]["sha256"]},
            "ppa_version": pins["ppa_version"],
            "files": [(f"score/{n}", sha256(read_bytes(f"svgolf/score/{n}")))
                      for n in ("ppa.py", "ppa_pins.json", "canon.ys", "svgolf.ys", "svgolf_seq.ys")]}


def rating_build_sentence(here):
    """The score card's line on the build the numbers come from (task pages), from `rating_build()`."""
    b = rating_build()
    y, a, d = b["yosys"], b["abc"], b["determinism"]
    o = d["other_build"]
    return (f"Rated with Yosys {esc(y['version'])} (git {code(y['git_sha1'][:8])}, {esc(y['build'])}, "
            f"{esc(y['compiler'])}) and its {code(a['binary'])} ({esc(a['version'])}): the flow is deterministic on "
            f"that build (measured on {d['designs']} designs). Another build of the same version can break ABC's ties "
            f"differently (measured: {o['designs_differing']} {esc(o['task'])} designs, up to "
            f"{o['max_delay_change_pct']:g}% in delay), so a number made on another platform may differ slightly: "
            + page.link(rel_link(here, f"rules.html#{RATING_BUILD_ANCHOR}"), "the build and its hashes") + ".")


def rating_build_html():
    """The rules page's section on the build the ranked numbers are rated with, from `rating_build()`: every binary
    and pinned file with its sha256."""
    b = rating_build()
    y, a, d = b["yosys"], b["abc"], b["determinism"]
    o = d["other_build"]
    rows = [page.Row(["Yosys", f"{code(y['version_line'])}<br>{esc(y['build'])}, {esc(y['compiler'])}",
                      code(y["sha256"])]),
            page.Row([code(a["binary"]), f"{esc(a['version'])}: {code(a['version_line'])}<br>{esc(a['build'])}",
                      code(a["sha256"])]),
            page.Row(["liberty", code(b["liberty"]["file"]), code(b["liberty"]["sha256"])])]
    rows += [page.Row([code(f), "the file as in the repository" + (f" ({code(b['ppa_version'])})"
                                                                   if f.endswith("ppa_pins.json") else ""), code(h)])
             for f, h in b["files"]]
    return (f'<section><h2 id="{RATING_BUILD_ANCHOR}">The build ratings use <a class="anchor" '
            f'href="#{RATING_BUILD_ANCHOR}" aria-label="link to this section">#</a></h2>'
            f"<p>Every ranked number on the board and on this site (the sky130 A0′ area and time, and with them par, "
            f"the record and under par) is made by ONE build of the tools (decided {esc(b['decided'])}). The flow is "
            f"deterministic on that build: the same design text gives the same area, time and netlist on every run "
            f"(measured {esc(d['measured'])} on {d['designs']} designs, {d['runs']} runs: {esc(d['what'])}). Another "
            f"build of the same Yosys version can break ABC's ties differently ({esc(o['cause'])}): under "
            f"{esc(o['build'])}, {o['designs_differing']} of the {d['designs']} designs, all {esc(o['task'])}, moved by "
            f"up to {o['max_delay_change_pct']:g}% in delay and {o['max_area_change_pct']:g}% in area. So a number you "
            f"make on another platform may differ slightly from the board's; the same build gives it bit for bit. "
            f"The build is not pinned to a slower portable one: get as close to it as you like.</p>"
            + page.table(["what", "version, build", "sha256"], rows) + "</section>")


def time_words(t, unit=""):
    """What the ranked time of task `t` is, with `unit` (' in ns') after the quantity: the critical-path delay
    (combinational), the latency in cycles times the period (a latency kind), the period itself (a reactive task:
    one decision per cycle)."""
    if not metrics.is_clocked(t.task):
        return f"the critical-path delay{unit}"
    if metrics.has_latency(t.task):
        return f"the latency in cycles × the register-to-register clock period{unit}"
    return f"the register-to-register clock period{unit}, one decision per cycle"


def asap7_banner(here):
    """The ASAP7 view's line at the top of a page that shows golf scores (shown in that view only)."""
    return ('<div class="pdk-asap7 pdk-banner"><p><strong>Golf scores on ASAP7</strong>, a predictive 7 nm library: '
            "never fabricated, and like sky130's score it counts no wires. sky130, a real 130 nm process, is the "
            "default. " + page.link(rel_link(here, f"rules.html#{ASAP7_ANCHOR}"), "How ASAP7 is scored, and its quirks")
            + ".</p></div>")


def asap7_words(here, *, short=False):
    """What the ASAP7 view's numbers are, said where they appear: a predictive 7 nm library, never fabricated,
    wire-free like sky130's score, with a link to how it is scored and its quirks (the rules page)."""
    link = page.link(rel_link(here, f"rules.html#{ASAP7_ANCHOR}"), "how ASAP7 is scored, and its quirks")
    if short:
        return f"ASAP7: a predictive 7 nm library, never fabricated; no wires, like sky130's score ({link})."
    return ("<strong>ASAP7 view.</strong> These numbers are on ASAP7 (asap7sc7p5t), a predictive 7 nm library made for "
            "research: it has never been fabricated, so no chip can confirm them. Like sky130's score they count no "
            f"wires. sky130, a real 130 nm process, is the default view ({link}).")


def score_definition(t):
    clocked = metrics.is_clocked(t.task)
    time = time_words(t, " in ns")
    # score/ppa.py, the clocked flow (`--seq`): the period is the latest arrival at an output or at a flop's D (plus
    # setup), over paths that start at an input or at a flop's Q
    period = ("The clock period (what score/ppa.py calls the register-to-register period) is the longest path from "
              "an input or a flip-flop to an output or a flip-flop (clock-to-Q and setup included), so paths from the "
              "inputs and to the outputs count too, not only the paths between two flip-flops. " if clocked else "")
    lib = PDK_NAME[t.pdk]
    extra = (" " + asap7_words(t.page) + " " if t.pdk == "asap7" else " ")
    return (f"<strong>Score</strong> = area × time: the {lib} cell area of the scored netlist in µm² "
            f"{'(flip-flops included) ' if clocked else ''}times {time}, from the pinned flow, so "
            f"{esc(combined.UNIT)}. Lower is better. "
            + ("It is the one ranked number: " if t.pdk == "sky130" else "In this view ")
            + "Par (the best proved reference's score, the bar to beat), Record (the best accepted score so far, par "
            "while no submission beats it), Under par (how far the record is below par, as a share of par's score) and "
            + ("the leaderboard use it. " if t.pdk == "sky130" else
               "the leaderboard use it; the records' ranked score is sky130's, the default view. ")
            + "The Pareto "
            "front, area in GE (NAND2 gate equivalents), depth and the other numbers are for exploring, "
            f"under {page.link('#explore', 'compare the designs')}; "
            f"{page.link(rel_link(t.page, REPRODUCE_PAGE), 'reproduce a score')} says how to get the same numbers."
            + extra + period + rating_build_sentence(t.page))


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
        start = (f"Par is the proved reference {code(t.par['stem'])}, with no {PDK_NAME[t.pdk]} weighing yet (its extra GE "
                 f"columns: {esc(ge(t.par['score']['area_mge']))}, depth {t.par['score']['depth']})." if p
                 else "There is no par yet.")
        return (f'<div class="chart-slot empty" id="over-time" data-hook="score-chart"><p>No design of this task '
                f"has {PDK_A[t.pdk]} weighing yet, so the chart has nothing to draw: the score needs the "
                f"{PDK_NAME[t.pdk]} area and time. {start}</p><p class=\"small\">{score_definition(t)}</p></div>")
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
        rows.append([esc((d["date"] or "–")[:10]), page.link(d["href"], esc(d["name"])), esc(kind_text(d)),
                     esc(combined.fmt(d["m"]["adp"])), esc(breakdown(d, t))])
    for d in lv:
        rows.append(['<span class="muted">–</span>', page.link(d["href"], esc(d["name"])), esc(kind_text(d)),
                     esc(combined.fmt(d["m"]["adp"])), esc(breakdown(d, t))])
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
              "first entries, dated by when they joined the task."
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
    return (f'<span class="label">{pdk_text("", "ASAP7 · ")}area × time · {nocase(esc(combined.UNIT))} · lower is '
            f'better</span>{tog}')


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
    numbers at each point, by score (the scaling view, `scaling_html`, follows it on the page: sky130 only)."""
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
            + tables + data_script(page_data(t), "task-data"))


def scaling_metrics(t):
    """The metrics the scaling view offers (those its lines have; not the proof's length, which is one
    number for every point), in the explorer's order; the first is drawn by the server."""
    have = {k for ln in t.lines for p in ln["pts"] for k in p["m"]}
    return [m for m in metric_table(t) if m.key in have and m.key != "proof_lines"]


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
            '<p class="pdk-asap7 pdk-note small">On sky130 in either view: the designs are measured at the other '
            "points on sky130 alone (score/measured/), and the ASAP7 view weighs each design at the scoring point "
            "only.</p>"
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
    combined score (`score_key`; equal scores share a rank), with par's row (no rank) in its place
    by score: under the records that beat par, above the rest (a record that only ties par is no
    record). The first record is highlighted as the lead only when it beats par (else the record is
    par). With no par score, par's row comes last. The bar is the score against the worst one shown."""
    ranked = sorted((d for d in t.designs if d["kind"] == "record"), key=score_key)
    p = par_design(t)
    par_exact = p["exact"] if p else None
    shown = [d["exact"] for d in ranked + ([p] if p else []) if d["exact"] is not None]
    worst = max(shown) if shown else None
    ref_hashes = {r["sha256"] for r in t.refs}

    def beats_par(d):
        return par_exact is None or (d["exact"] is not None and d["exact"] < par_exact)
    rows, prev, rank, par_at = [], None, 0, None
    for k, d in enumerate(ranked, 1):
        if par_at is None and par_exact is not None and not beats_par(d):
            par_at = len(rows)
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
                                  esc(breakdown(d, t) or f"{lb.fmt_ge(round(d['m']['area_ge'] * 1000))} GE, depth {d['m']['depth']}"),
                                  d["exact"] / worst if worst and d["exact"] is not None else None,
                                  "lead" if rank == 1 and d["exact"] is not None and beats_par(d) else None))
    if t.par:
        s = t.par["score"]
        name = page.link(f"#ref-{t.par['stem']}", code(t.par["stem"]))
        rows.insert(len(rows) if par_at is None else par_at,
                    page.BoardRow("", name, f"{page.badge('par', 'par')} proved reference",
                                  combined.fmt(p["m"].get("adp")) if p else "–",
                                  esc((breakdown(p, t) if p else "") or f"{lb.fmt_ge(s['area_mge'])} GE, depth {s['depth']}"),
                                  p["exact"] / worst if p and worst and p["exact"] is not None else None, "par"))
    if t.par and p and p["exact"] is not None:
        par_text = (f"Par, the bar to beat, is the proved reference {code(t.par['stem'])}: "
                    f"{esc(combined.fmt(p['m']['adp']))} {esc(combined.UNIT)} ({esc(breakdown(p, t))}).")
    elif t.par:
        par_text = (f"Par is the proved reference {code(t.par['stem'])}; no design of this task has {PDK_A[t.pdk]} "
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
            esc(f"{m['area_um2']:.{3 if t.pdk == 'asap7' else 1}f}") if "area_um2" in m else "–",
            esc(str(m.get("time_ps", "–"))),
            esc(lb.fmt_ge(r["area_mge"])), str(r["depth"]), str(r["proof_lines"]), assisted(r),
            record_link(t, here, d["id"]), file_links(here, base, (".sv", ".lean"))],
            cls="frontier-row" if k == 1 else None))
    if rows:
        parts.append(page.details("every column: area, time, proof lines, assisted by, files", page.table(
            heads("#", "player", "date", f"score ({combined.UNIT})", "area (µm²)", "time (ps)", "area (GE)", "depth",
                  "proof lines", "assisted by", "record", "files"), rows, numeric=(0, 3, 4, 5, 6, 7, 8))))
    if t.board["unranked"]:
        muted = '<span class="muted">–</span>'
        urows = [[esc(r["player"]), esc(lb.fmt_area(r)) if lb.row_area(r) is not None else muted,
                  esc(str(r["time_ps"])) if r["time_ps"] is not None else muted,
                  esc(lb.fmt_ge(r["area_mge"])), str(r["depth"]),
                  record_link(t, here, r["record_hash"]), esc(r["reason"])] for r in t.board["unranked"]]
        lib = PDK_NAME[t.pdk]
        parts.append(page.details(f"not ranked: no {lib} score, or not comparable", (
            f"<p>A record ranks on its {lib} area and time, weighed under the pinned flow, the current {lib} "
            "pins and the task's input drive, at the task's scoring point. These are not comparable until they "
            "are checked again"
            + (" (or, in the ASAP7 view, until their ASAP7 columns are measured)" if t.pdk == "asap7" else "")
            + ".</p>"
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
    """The extra GE columns of a score as one cell: '112.000 · 33' (area in GE, depth in gates). The space after
    the dot is a plain one: a table cell does not wrap (td.num), a phone's stacked row may, after the dot."""
    return f"{esc(lb.fmt_ge(s['area_mge']))}\u00a0· {s['depth']}" if s else "–"


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

        def cells(ref=ref, s=s):
            """The cells that change with the library (the view `t.pdk`): par's badge, the score, area and time, vs
            par."""
            d = design_of(t, "reference", ref["stem"])
            return [page.badge("par", "par") if t.par is ref else "", score_cell(d), *sky_cells(t, d),
                    ("par" if t.par is ref else esc(vs_par_text(t, d, s["area_mge"]))) if s and t.par else "–"]
        sky = cells()
        with t.view("asap7"):
            a7 = cells()
            a7_par = t.par is ref
        tag, score, area, time, vsp = (dual(a, b, inline=True) if a or b else "" for a, b in zip(sky, a7))
        tags = tag
        if ref["same_design_as"]:
            tags += " " + page.badge(f"same design as {ref['same_design_as']}", "layer")
        base = f"tasks/{t.name}/reference/{ref['stem']}"
        meta = (f'<span class="cell-meta">tactics: {esc(", ".join(ref["tactics"]))}</span>'
                if ref["tactics"] else "")
        if ref["record_hash"]:
            meta += f'<span class="cell-meta">record: {record_link(t, here, ref["record_hash"])}</span>'
        cls = " ".join(c for c, on in (("par-row", t.par is ref), ("par-a7", a7_par)) if on) or None
        rows.append(page.Row([
            design_cell((code(ref["stem"]) if t.preview else page.link(rel_link(here, reference_page(t, ref)),
                                                                        code(ref["stem"]))) + " " + tags,
                        md_inline(ref["description"]), meta), score,
            area, time, ge_depth_cell(s), vsp,
            str(ref["proof_lines"]), file_links(here, base, (".sv", ".lean"))],
            cls=cls, id_=f"ref-{ref['stem']}"))
    return ("<p>Proved and accepted designs that ship with the task, written or adapted by the maintainers. They are "
            "the first entries, and <strong>par</strong>, the bar to beat, is the one with the best score "
            f"(area × time, {esc(combined.UNIT)}, from the {pdk_text('sky130', 'ASAP7')} area and time; a design "
            f"without {pdk_text('a sky130', 'an ASAP7')} "
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
        flag = page.badge("banned operator", "banned") if b["banned"] else ""
        if s:
            where = ge_depth_cell(s)
        else:
            where = '<span class="muted">' + (f'scored at {esc(", ".join(b["points"]))} only' if b["points"]
                                              else "not scored") + "</span>"
        def cells(b=b, s=s):
            d = design_of(t, "baseline", b["stem"])
            return [score_cell(d), *sky_cells(t, d), esc(vs_par_text(t, d, s["area_mge"])) if s and t.par else "–"]
        sky = cells()
        with t.view("asap7"):
            a7 = cells()
        score, area, time, vsp = (dual(a, b_, inline=True) for a, b_ in zip(sky, a7))
        rows.append(page.Row([design_cell(code(b["stem"]) + " " + flag, md_inline(b["description"])), score,
                              area, time, where, vsp,
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
            # (the SRT attacks, Apache-2.0 WITH SHL-2.1) or the MIT grant (the sorter's attacks). The block is then
            # the file byte for byte, so it names the file (`data-src`, which the tests compare with it)
            if "SPDX-License-Identifier" in src or "Permission is hereby granted" in src:
                design = page.details("the design, with its licence and provenance notices",
                                      page.code_block(src, "sv", src=r["sv"]), cls="reveal")
            else:
                design = page.details("the design, with its comments left out",
                                      page.code_block(strip_sv_comments(src), "sv"), cls="reveal")
            items.append(f'<li><p class="reject-head">{code(r["stem"] + ".sv")} '
                         f'<span class="muted">({esc(r["kind"])}, stopped at {stage})</span>: {text}</p>{design}</li>')
        parts.append(f'<h5 id="reject-{gid}">{esc(title)}</h5><p class="muted">{intro}</p>'
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


# Step 0 of every "How to submit", of the tutorial and of llms.txt: the tools, then the two one-time
# commands. The versions are read from the repository (lean-toolchain, requirements.txt, the flow pin).
LAKE_BUILD_COST = ("about 6 minutes and 1 GB of disk the first time, on a laptop that already had the Lean toolchain "
                   "(README.md's Step 0 says what was measured where; elan's first download of the toolchain comes on "
                   "top): Lake clones proglib (formerly lean-surfaces) and its packages from "
                   "github.com, so it needs network access there, and builds the LeanModels.Sv modules svGolf "
                   "uses; Mathlib is cloned, never built")
LATENCY_KINDS = metrics.LATENCY_KINDS               # check.py's: a clocked task's Goal takes the latency


def prerequisites(site):
    """{"lean", "yosys", "pyslang"}: the pinned versions Step 0 names."""
    lean = read_text("svgolf/lean-toolchain").strip()
    m = re.match(r"Yosys (\S+)", (site.flow or {}).get("yosys") or "")
    yosys = m.group(1) if m else None
    pin = next((ln.strip() for ln in read_text("svgolf/requirements.txt").split("\n")
                if ln.strip() and not ln.startswith("#")), None)
    if yosys is None or pin is None:
        raise BuildError("Step 0: no Yosys version in the flow pin, or no package in svgolf/requirements.txt")
    return {"lean": lean, "yosys": yosys, "pyslang": pin}


def clone_commands(repo_url):
    """How a command block gets to the root of svGolf: the clone (with a public repository), else
    `cd svgolf` from the repository's root."""
    if not repo_url:
        return "cd svgolf\n"
    top = posixpath.basename(repo_url.rstrip("/"))
    top = top[:-len(".git")] if top.endswith(".git") else top
    return f"git clone {repo_url}\ncd {top}" + ("/svgolf\n" if LAYOUT == "inside" else "\n")


def step0_html(site, here, id_=None):
    """Step 0: what to install, then (from the clone) `lake build` and the liberty, once per machine. `id_`: an
    anchor on its first line (How to submit's, `step-0`)."""
    v = prerequisites(site)
    tools = ("<ul>"
             f"<li>{page.link('https://github.com/leanprover/elan', 'elan')}, which installs the Lean toolchain "
             f"that <code>lean-toolchain</code> pins (<code>{esc(v['lean'])}</code>) on first use;</li>"
             f"<li>Yosys {esc(v['yosys'])} with its <code>yosys-abc</code> (every pinned tool and file: "
             f"{page.link(rel_link(here, REPRODUCE_PAGE), 'Reproduce a score')});</li>"
             # check/postsynth.py tool(): "the postsynth stage needs Verilator 5, a C++ compiler, make and Yosys"
             "<li>Verilator 5, a C++ compiler and <code>make</code>, for the post-synthesis check (it compiles "
             "Verilator's model of the netlist);</li>"
             "<li>Python 3.12 with <code>python3.12 -m pip install -r requirements.txt</code> "
             f"(<code>{esc(v['pyslang'])}</code>, the extractor's SystemVerilog frontend).</li></ul>")
    cmds = (clone_commands(site.config.get("repo_url"))
            + "python3.12 -m pip install -r requirements.txt\n"
            "# the trusted Lean and the checker's evaluator\n"
            "lake build\n"
            "# the pinned sky130 liberty, checked by its hash\n"
            "python3.12 score/ppa.py --fetch-liberty\n")
    anchor = f' id="{esc(id_)}"' if id_ else ""
    return (f"<p{anchor}><strong>Step 0, once per machine.</strong> Install:</p>{tools}"
            + page.code_block(cmds, "bash", name="step 0", term=True)
            + f"<p class=\"small muted\"><code>lake build</code> takes {esc(LAKE_BUILD_COST)}.</p>")


def design_module(t):
    """The `Submission.Design` the checker generates for task `t` (check.py's design_module_text, without
    its trailing unsupported-construct check)."""
    stmt = t.task["statement"]
    if t.kind in LATENCY_KINDS:
        goal = (f"abbrev Goal (lat : …) : Prop :=\n  {stmt['constant']} design.sem lat ∧ "
                "lat <scoring point> = <your latency>")
    else:
        goal = f"abbrev Goal : Prop := {stmt['constant']} design.sem"
    return (f"import LeanModels.Sv.Ingest2\nimport {stmt['module']}\n\nnamespace Submission\n"
            "load_design_sv2 design from \"<the envelope of your .sv>\"\n"
            f"{goal}\nend Submission\n")


# check.py's `-- svgolf-latency: n` header (LATENCY_HEADER, with its one decimal value) and the solution's latency
# definition `Submission.lat` (LATENCY_DEF), as a line of par's proof: the skeleton of a latency kind shows that pair
LATENCY_LINE = re.compile(r"^--[ \t]*svgolf-latency:[ \t]*([1-9][0-9]*)[ \t]*$", re.M)
LATENCY_DEF_LINE = re.compile(r"^def lat [^\n]*$", re.M)
# the v2 reduction a latency kind's proof ends in (SvGolf/SeqV2.lean) and the arguments it takes, in order
LATENCY_REDUCTION = {
    "tx-family": ("TxTask.satisfiedAtV2_of_phases",
                  ("interface, discipline, TerminatesPU, 1 ≤ lat, a", "PhaseModel, the shape at every power-up,",
                   "MooreOutDep (combDeps_of_ffOnly), XSafe; a complete one:")),
    "stream-family": ("StreamTask.satisfiedAtV2_of_phases",
                      ("interface, discipline, TerminatesPU, 1 ≤ count,", "count ≤ lat, spec keeps the length, a",
                       "PhaseModel, the shape at every power-up,", "MooreOutDep (combDeps_of_ffOnly), XSafe; a",
                       "complete one:")),
}


def latency_example(t):
    """(n, the `def lat …` line) of par's proof: the value of its `-- svgolf-latency:` header and its latency
    definition, the skeleton's example of the pair. None without par, or when par's proof has not exactly one of
    each (the skeleton then shows placeholders)."""
    if not t.par:
        return None
    src = read_text(t.par["lean"])
    n, d = LATENCY_LINE.findall(src), LATENCY_DEF_LINE.findall(src)
    return (int(n[0]), d[0]) if len(n) == 1 and len(d) == 1 else None


def latency_skeleton(t, ref):
    """The outline of a latency kind's `Solution.lean`: the header line, the latency definition `lat` (par's as the
    example), and the goal `Goal lat`, whose second conjunct `rfl` closes when the header is `lat` at the scoring
    point; the statement goes through the kind's v2 reduction (`LATENCY_REDUCTION`)."""
    names = [p["name"] for p in t.task["parameters"]]
    ex = latency_example(t)
    n, lat_def = ex if ex else ("<n>", f"def lat ({' '.join(names)} : Nat) : Nat := <your latency>")
    what = (f"-- your latency in cycles, one Nat per parameter (here the\n"
            f"-- reference's, {t.par['stem']}); the header line above is its\n"
            f"-- value at the scoring point, {point_text(t.point)}\n" if ex else
            "-- your latency in cycles, one Nat per parameter; the header\n"
            f"-- line above is its value at the scoring point, {point_text(t.point)}\n")
    reduction, args = LATENCY_REDUCTION[t.kind]
    return (f"-- svgolf-latency: {n}\n"
            "import Submission.Design\n"
            "import SvGolf.SeqV2   -- the v2 reductions, combDeps_of_ffOnly\n\n"
            "namespace Submission\n"
            "open LeanModels.Sv SvGolf\n\n"
            + what
            + f"{lat_def}\n\n"
            "-- in `namespace Submission`, this is\n"
            "-- `theorem Submission.solution : Submission.Goal Submission.lat`\n"
            "theorem solution : Goal lat := by\n"
            "  -- the statement at every in-range point, and `lat` at the\n"
            "  -- scoring point is the header's number (`rfl`)\n"
            "  refine ⟨fun p hp => ?_, rfl⟩\n"
            f"  -- {reduction}:\n"
            + "".join(f"  -- {a}\n" for a in args)
            + f"  -- {ref}\n\n"
            "end Submission\n")


def solution_skeleton(t):
    """The outline of a `Solution.lean` (a skeleton: the proof is the player's): the sv_comb tactics for a
    combinational task, the reactive reduction `ReactTask.satisfiedAt_of_rank` for a reactive one, the latency
    header, `lat` and the v2 phase reduction for a latency kind (`latency_skeleton`)."""
    ref = f"tasks/{t.name}/reference/{t.par['stem']}.lean" if t.par else "a reference proof"
    if t.kind in LATENCY_KINDS:
        return latency_skeleton(t, ref)
    if t.kind == "react-family":
        return ("import Submission.Design\n"
                "import SvGolf.React        -- the reduction, MooreOut\n"
                "import SvGolf.RoundRobin   -- lowest set bit, thermometer\n\n"
                "namespace Submission\n"
                "open LeanModels.Sv SvGolf\n\n"
                "-- in `namespace Submission`, this is\n"
                "-- `theorem Submission.solution : Submission.Goal`\n"
                "theorem solution : Goal := by\n"
                "  intro N hN\n"
                "  -- satisfiedAt_of_rank: interface, discipline, TerminatesPU,\n"
                "  -- a rank model, the power-up shape, XSafe; a complete one:\n"
                f"  -- {ref}\n\n"
                "end Submission\n")
    return ("import Submission.Design\n"
            "import SvGolf.Comb\n"
            "import LeanModels.Sv.CombEqTactic   -- the sv_comb tactics\n"
            "import LeanModels.Sv.CombLib        -- the plain-Lean library\n\n"
            "namespace Submission\n"
            "open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib\n"
            "open LeanModels.Sv.CombEq SvGolf\n\n"
            "-- in `namespace Submission`, this is\n"
            "-- `theorem Submission.solution : Submission.Goal`\n"
            "theorem solution : Goal := by\n"
            "  -- your proof; a complete one:\n"
            f"  -- {ref}\n\n"
            "end Submission\n")


SEQ_SECTION_NO = 19                                  # PROVING.md's section on the latency kinds (`proving_anchor`)


def proving_anchor(number):
    """The anchor of PROVING.md's section `number` on proving.html: its `## <number>. ` heading, slugged as the
    page slugs it, so that a link to it follows the heading's text."""
    m = re.search(rf"^## ({number}\. .+)$", read_text("svgolf/PROVING.md"), re.M)
    if m is None:
        raise BuildError(f"svgolf/PROVING.md: no section '## {number}. …' (the clocked kinds' pages link it)")
    return md.Slugger().slug(m.group(1))


def lean_contract_html(t, here, skeleton=None):
    """What the Lean file must be: the generated module it imports, a skeleton, what is free. A latency kind's
    goal takes the solution's latency `lat`, pinned at the scoring point by its header line (check.py's
    goal_text). `skeleton`: (href, words) when the page's "Start a new design" card shows a Solution.lean (the
    README's skeleton, or the whole file): the contract then points to it rather than show a second skeleton, and
    leaves the proving guide's section to the card's route, which names it (2026-11-09: one statement of each)."""
    stmt = t.task["statement"]
    first = rel_link(here, "proving.html") + "#0-the-loop"
    if t.kind in LATENCY_KINDS:
        p0 = " ".join(str(t.point[p["name"]]) for p in t.task["parameters"])     # check.py's goal_text order
        goal = (f"<code>Goal lat</code> unfolds to <code>{esc(stmt['constant'])} Submission.design.sem lat ∧ lat "
                f"{esc(p0)} = n</code>: the task's statement of your design at your latency <code>lat</code> (cycles, a "
                f"function of the parameters), and its value at the scoring point ({esc(point_text(t.point))}), the "
                "<code>n</code> of your header line <code>-- svgolf-latency: n</code>, which the score takes as the "
                # check.py parse_latency reads the solution's Lean text, never the .sv
                "cycles (the checker reads the latency from this file, never from the <code>.sv</code>)")
        proves = "<code>Goal lat</code>"
        qualified = "<code>theorem Submission.solution : Submission.Goal Submission.lat</code>"
        fixed = ("the module name <code>Submission</code>, the <code>import Submission.Design</code> header, the "
                 "definition <code>lat</code> (one <code>Nat</code> per parameter, in the task's order), the theorem "
                 "<code>solution : Goal lat</code>@Q and exactly one line <code>-- svgolf-latency: n</code> (n a decimal "
                 "number of cycles, at least 1) are fixed. ")
        seq = rel_link(here, "proving.html") + "#" + proving_anchor(SEQ_SECTION_NO)
        guide = (f"{page.link(seq, f'The proving guide, section {SEQ_SECTION_NO}')}, walks through the clocked route "
                 "on the two references.")
    else:
        goal = (f"<code>Goal</code> unfolds to <code>{esc(stmt['constant'])} Submission.design.sem</code>, the task's "
                "statement of your design")
        proves = "<code>Goal</code>"
        qualified = "<code>theorem Submission.solution : Submission.Goal</code>"
        fixed = ("the module name <code>Submission</code>, the <code>import Submission.Design</code> header and the "
                 "theorem <code>solution : Goal</code>@Q are fixed. ")
        guide = (f"{page.link(first, 'The proving guide, section 0')}, shows the loop: stage the design, print its "
                 "equations with a probe file, then prove." if t.kind != "react-family" else
                 f"{page.link(rel_link(here, 'proving.html') + '#' + REACT_SECTION, 'The proving guide, section 20')}, "
                 "walks through the reactive route on the reference.")
    head = (f"<p><strong>The Lean file.</strong> The checker extracts your <code>.sv</code> itself and writes "
            f"the trusted module <code>Submission.Design</code>; {goal}:</p>"
            + page.code_block(design_module(t), "lean", name="Submission.Design (generated: you never write it)"))
    free = "File names and paths are free (here <code>solution.sv</code> and <code>Solution.lean</code>); "
    if skeleton:
        href, words = skeleton
        return (head + f"<p>Your <code>Solution.lean</code> imports it and proves {proves}, as "
                f"{page.link(href, words)} shows. " + free
                + fixed.replace("@Q", f" (in <code>namespace Submission</code>, {qualified})").rstrip() + "</p>")
    return (head + f"<p>Your <code>Solution.lean</code> imports it and proves {proves}:</p>"
            + page.code_block(solution_skeleton(t), "lean", name="Solution.lean (a skeleton)")
            + "<p>" + free + fixed.replace("@Q", "") + guide + "</p>")


def unproved_latency(t):
    """The `--latency` value of a latency kind's `--unproved` run in the commands shown (check.py refuses that run
    without one, a usage error): par's latency at the scoring point (`latency_example`), else a placeholder.
    None for a task whose goal takes no latency (check.py refuses `--latency` there)."""
    if t.kind not in LATENCY_KINDS:
        return None
    ex = latency_example(t)
    return str(ex[0]) if ex else "YOUR_LATENCY"


def wrap_command(cmd, width=58):
    """A one-line shell command as lines of at most `width` characters, each but the last ending in ` \\`, the
    next indented by four spaces (How to submit's code block sits in a column)."""
    lines = [""]
    for w in cmd.split(" "):
        if lines[-1].strip() and len(lines[-1]) + 1 + len(w) > width:
            lines.append("    " + w)
        else:
            lines[-1] = f"{lines[-1]} {w}" if lines[-1].strip() else lines[-1] + w
    return " \\\n".join(lines) + "\n"


def wrap_comment(text, width=60):
    """A `# comment` line of How to submit's code block as lines of at most `width` characters, the next ones
    starting `#    `, as the step comments are written."""
    lines = []
    for w in text.split(" "):
        if lines and len(lines[-1]) + 1 + len(w) <= width:
            lines[-1] += " " + w
        else:
            lines.append(("#    " if lines else "# ") + w)
    return "\n".join(lines) + "\n"


def submit_commands(t, card=None):
    """The four commands of a task's "How to submit", from the root of svGolf (Step 0 got there): the golfing loop,
    1. the run without a proof, 2. the real check, 3. the record. With `card` (the task's NewDesignCard) the first two
    are the card's own (`NewDesignCard.commands`: the README's, with the options its proof route uses), so the page
    shows one form of each command; without, a clocked task is weighed through the clocked flow (`--seq`; its time is
    the register-to-register period) and a latency kind's `--unproved` run takes the latency it means to claim
    (`--latency n`, par's as the example)."""
    name = t.name
    # check.py: incomplete_reasons (light postsynth), then "check: accepted, but the check was INCOMPLETE"
    real = ("# the real check: prints \"accepted\": true; its\n"
            "#    post-synthesis check is LIGHT by default (a subset of\n"
            "#    the vectors, for local feedback), so stderr also says\n"
            "#    \"accepted, but the check was INCOMPLETE ... rerun with\n"
            "#    --postsynth full\": expected, since step 3 runs the\n"
            "#    full one itself\n"
            f"python3.12 check.py tasks/{name} solution.sv Solution.lean\n")
    record = ("# record it: the whole check again, full and sandboxed\n"
              f"python3.12 leaderboard/leaderboard.py add --task {name} \\\n"
              "    --player YOUR_HANDLE --assisted-by \"TOOL OR MODEL\" \\\n"
              "    --sv solution.sv --lean Solution.lean \\\n"
              "    --notes \"YOUR DESIGN IN ONE LINE\"\n")
    par_n = unproved_latency(t)
    if card is not None:
        (golf_cmd, golf_note), (check_cmd, check_note) = card.commands(name)
        golf = (wrap_comment("the golfing loop, no Lean" + (f": {golf_note}" if golf_note else ""))
                + wrap_command(golf_cmd))
        given = re.findall(r"(?<!\S)--latency (\S+)", check_cmd)
        # check.py's usage rule: `--latency n` exactly on a latency kind's --unproved run
        if len(given) != (1 if par_n is not None else 0):
            raise BuildError(f"{card.where}: its run without a proof must give `--latency n` "
                             + ("once (the task's goal takes a latency)" if par_n is not None else
                                "never (the task's goal takes no latency)"))
        n = given[0] if given else None
        step1 = wrap_command(check_cmd)
        note = f"#    {check_note}\n" if check_note else ""
    else:
        golf = ("# the golfing loop: ranked area and period in seconds, no Lean\n"
                f"python3.12 score/ppa.py solution.sv --task tasks/{name} \\\n"
                "    --seq --path\n" if metrics.is_clocked(t.task) else
                "# the golfing loop: ranked area and delay, ~2 s, no Lean\n"
                f"python3.12 score/ppa.py solution.sv --task tasks/{name} \\\n"
                "    --no-mapped --path\n")
        n = par_n
        step1 = (f"python3.12 check.py tasks/{name} solution.sv --unproved\n" if n is None else
                 f"python3.12 check.py tasks/{name} solution.sv --unproved \\\n    --latency {n}\n")
        note = ""
    return (golf
            + "# 1. no proof needed; never accepts; exits 0 when every\n"
            + ("#    stage passed, ending with area x time and par\n" if n is None else
               "#    stage passed, ending with area x time and par;\n"
               "#    --latency: the cycles you mean to claim"
               + (f" ({n}: par's)\n" if n == par_n and n.isdigit() else "\n"))
            + note + step1
            + "# 2. " + real[2:]
            + "# 3. " + record[2:])


def handle_max():
    """The longest handle leaderboard.py takes, read from its PLAYER_RE (a first letter or digit, then up to n of
    letters, digits and `._-`): what "How to submit" says of YOUR_HANDLE. Another shape of the rule fails the build."""
    m = re.fullmatch(r"\[A-Za-z0-9\]\[A-Za-z0-9\._-\]\{0,(\d+)\}", lb.PLAYER_RE.pattern)
    if m is None:
        raise BuildError(f"leaderboard.py's PLAYER_RE {lb.PLAYER_RE.pattern!r} is not the rule How to submit states")
    return 1 + int(m.group(1))


def ppa_loop_html(t):
    """What score/ppa.py does and does not check, under How to submit's commands on a page without a "Start a new
    design" card (the tutorial's); a page with one says it under the card's text on its two commands, NEW_DESIGN_PPA."""
    seq = " (with <code>--seq</code>, the clocked flow, the register-to-register period)" if metrics.is_clocked(t.task) \
        else ""
    return ("<p><code>score/ppa.py</code> is the inner loop of golfing: it runs the source gate and the pinned flow and "
            f"prints the ranked numbers, <code>area_um2_sky130</code> and <code>delay_ps_sky130</code>{seq}. It does "
            "not check the banlist, the 4-state rules, whether ls-sv can read the design, the post-synthesis simulation "
            "or the task's function, and needs no proof: run step 1 before you prove.</p>")


# the same facts under the "Start a new design" card's text on its two commands (which How to submit shows first; that
# text says what the first one prints, and step 1's comment what the second ends with)
NEW_DESIGN_PPA = ("<code>score/ppa.py</code> is the inner loop of golfing; its ranked numbers are "
                  "<code>area_um2_sky130</code> and <code>delay_ps_sky130</code> in what it prints. It runs only the "
                  "source gate and the pinned flow: it does not check the banlist, the 4-state rules, whether ls-sv can "
                  "read the design, the post-synthesis simulation or the task's function. Step 1 does, still without a "
                  "proof.")


def commands_once(t, body_html, cmds):
    """Each command How to submit shows (`cmds`, its code block, and the copy of par's pair) is on the task page once
    and in one form (2026-11-09: each fact once; 2026-11-11: How to submit holds all four): a command is known by its
    program and first arguments (`python3.12 check.py tasks/<t> solution.sv --unproved`), so a second form of it
    anywhere on the page fails the build. Not on the tutorial, whose walk-through runs them again on purpose."""
    if t.listing == "tutorial":
        return
    joined = lambda x: x.replace(" \\\n    ", " ")            # noqa: E731  (wrap_command's continuation lines)
    text = joined(html.unescape(re.sub(r"<[^>]+>", "", body_html)))
    for ln in (joined(cmds) + reference_copy(t)).split("\n"):
        if not ln or ln.startswith("#"):
            continue
        key = " ".join(ln.split()[:5])
        # the program and its arguments, also without the interpreter (`score/ppa.py solution.sv --task tasks/<t>`)
        bare = key.split(" ", 1)[1] if key.startswith("python3.12 ") else key
        for k in dict.fromkeys((key, bare)):
            n = len(re.findall(rf"{re.escape(k)}(?![\w/.-])", text))
            if n != 1:
                raise BuildError(f"{t.page}: How to submit's command `{k} ...` is on the page {n} times; each "
                                 "command is on a task page once, in How to submit")


def submit_html(site, t, repo_url, card=None, skeleton=None, checks=""):
    """How to submit, the path of a first submission (2026-11-11, from the second newcomer study): the two files;
    Step 0; the copy of par's pair to start from; the four commands; what "done" is; what the first two do; the Lean
    file; where the record goes. Without a public repository (`repo_url` null) only the local flow is shown; with
    one, the clone and the pull request. `card`: the task's "Start a new design" card (NewDesignCard), whose two
    commands are the first two here and whose text on them (`checks`, new_design_parts) follows them; `skeleton`:
    (href, words) of the card's Solution.lean, which the Lean file then points to rather than show a second one."""
    here = t.page
    data_dir = f"leaderboard/data/{t.name}/"
    lat = t.kind in LATENCY_KINDS
    cmds = submit_commands(t, card)
    if repo_url:
        intro = ""
        hand_in = (f"Then open a pull request against {page.link(repo_url, esc(repo_url))} that adds them; CI "
                   "re-verifies it. There is no submission server: nothing is sent anywhere by these commands.")
    else:
        intro = ("<p><strong>Public submissions open when the svGolf repository is published.</strong> Until "
                 "then, this is the flow on a machine that has the repository: check a solution, then record "
                 "it locally.</p>")
        hand_in = "Nothing is sent anywhere: there is no submission server."
    if repo_url:
        where = (f"<code>{esc(data_dir)}</code>, the directory a pull request adds. {hand_in} For a private "
                 "trial, add <code>--data-dir DIR</code>: the record then goes to <code>DIR</code> and the "
                 "board stays as it is.")
    else:
        where = f"<code>{esc(data_dir)}</code>, the board of the machine it runs on. {hand_in}"
    # the two files (interface_html, lean_contract_html), before Step 0; after it, par's pair as the start (the
    # tutorial's walk-through, above, copies its own pair)
    files = ("<p><strong>You hand in two files</strong>: <code>solution.sv</code>, a module with the exact header "
             f"under {page.link('#interface', 'Interface')}, and <code>Solution.lean</code>, a Lean 4 proof that it "
             f"meets {page.link('#spec', 'the trusted statement')}" + (", at the latency you declare" if lat else "")
             + "." + (f" {page.link('#first-submission', 'Your first submission')}, above, copies a reference pair "
                      "and runs each command below with what it prints." if t.listing == "tutorial" else "") + "</p>")
    copy = reference_copy(t) if t.listing != "tutorial" else ""
    start = (f"<p><strong>Start from the reference pair</strong> under {page.link('#files', 'Files')}, "
             f"{code(t.par['stem'])}, a complete and accepted one: copy it, from the same directory:</p>"
             + page.code_block(copy, "bash", name="shell", term=True)) if copy else ""
    proof = f"write its proof ({page.link('#new-design', NEW_DESIGN)}, below, gives the route)" if card else \
        f"write its proof (the {page.link(rel_link(here, 'proving.html'), 'proving guide')} shows how)"
    then = (f"<p><strong>Then, for each design</strong>, from the same directory: find it without Lean and check it once "
            f"without a proof{', at the latency you mean to claim' if lat else ''} (the golfing loop and step 1), "
            f"{proof}, then check the pair and record it (steps 2 and 3):</p>")
    # leaderboard.py cmd_add: "added <task>/<hash12>: <player>, <score>, ..." once the record is written, else
    # "REFUSED: the submission was not added:" with the reasons
    done = (f"<p><strong>Done</strong>: step 3 prints <code>added {esc(t.name)}/HASH: YOUR_HANDLE, …</code> once the "
            "pair has passed the whole check, full and sandboxed, and its record is written (what it writes, and where: "
            "below); otherwise it prints <code>REFUSED</code> with the reasons and records nothing. Step 2's "
            "<code>\"accepted\": true</code>, with its INCOMPLETE line, is feedback for you, not a record.</p>")
    # the card's text on its two commands, under a lead-in that names them as How to submit's first two
    lead_in = "<strong>The golfing loop and step 1</strong>, the first two commands above. "
    checks = f"<p>{lead_in}{checks[3:]}" if checks.startswith("<p>") else (f"<p>{lead_in}</p>{checks}" if checks else "")
    loop = (checks + f"<p>{NEW_DESIGN_PPA}</p>") if card else ppa_loop_html(t)
    after = ("<p>Step 3 writes your record's three files (<code>.json</code>, <code>.sv</code> and "
             f"<code>.lean</code>, named by the record's hash) to {where} Repeat <code>--assisted-by</code> for "
             "each tool or AI system that helped, or leave it out.</p>"
             # leaderboard.py: PLAYER_RE, MAX_NOTES; the record page's "player" and "notes" rows, the board's player
             f"<p><code>YOUR_HANDLE</code> is your public name: the board and the record's page show it. It is 1 to "
             f"{handle_max()} characters, letters, digits, <code>.</code>, <code>_</code> or <code>-</code>, the first "
             f"a letter or a digit (<code>{esc(lb.PLAYER_RE.pattern)}</code>). <code>--notes</code> is optional: one "
             "line on the design "
             f"(at most {lb.MAX_NOTES} characters), shown on the record's page."
             # leaderboard.py add_submission: --from-check only outside leaderboard/data; README "Official records"
             + (" In a private trial (<code>--data-dir DIR</code>), <code>add --from-check RESULT.json</code> records "
                "the JSON that a <code>check.py … --postsynth full --ppa require</code> run printed instead of "
                "checking again; the board's own <code>leaderboard/data/</code> refuses a stored result."
                if repo_url else "") + "</p>")
    sandbox = ("<p><code>leaderboard.py add</code> runs the check with <code>--sandbox require</code>: the "
               "proof's Lean, the extractor, Yosys and Verilator must run inside the operating system's "
               "sandbox (Seatbelt on macOS, bubblewrap on Linux). Where that sandbox is missing or fails its "
               "self-test, the check stops with an infrastructure error and nothing is recorded. On such a "
               "machine, <code>--sandbox auto</code> runs the check without it (and says so on stderr), and "
               "<code>--sandbox off</code> skips it: your proof file then runs with your own privileges, and "
               "the record is for your own use, since an official record is made with the sandbox or not at "
               "all. <code>add</code> also weighs the ranked sky130 numbers, which need the pinned liberty "
               "(Step 0). On a shared machine whose Lean calls go through a wrapper, set "
               "<code>SVGOLF_LEAN_WRAP</code>; <code>check.py</code> and <code>leaderboard.py</code> both read "
               "it, and <code>SVGOLF_LEAN_WRAP_ONCE=1</code> takes the wrapper once for a whole run.</p>")
    return (intro + files + step0_html(site, here, id_="step-0") + start + then
            + page.code_block(cmds, "bash", name="shell", term=True) + done + loop
            + lean_contract_html(t, here, skeleton=skeleton) + after
            + page.details("the sandbox, and machines without one", sandbox))


def preview_html(t):
    """A preview's status line: why its submissions are not ranked yet (content/tasks/<t>.json)."""
    return f'<p class="preview-note"><strong>Preview.</strong> {md_inline(t.preview_note)}</p>'


def score_tips_html(site, t, here):
    """"What moves the score": content/tasks/<t>.json's `score_tips`, observations (Markdown inline, with
    placeholders), or "" when the task has none."""
    src = f"{CONTENT}/tasks/{t.name}.json"
    tips = (site.content(f"tasks/{t.name}.json") or {}).get("score_tips") or []
    if not tips:
        return ""
    items = "".join(f"<li>{md_inline(fill_placeholders(site, t, x, src), site.resolver(src, here))}</li>"
                    for x in tips)
    return ("<p>What players have seen move the ranked sky130 numbers: observations, not promises (the pinned flow "
            f"is the judge, and <code>score/ppa.py</code> measures a variant in seconds).</p><ul>{items}</ul>")


PROBE_FILE = """\
import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

namespace Submission
open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

example (N : Nat) (hN : 1 ≤ N) : CombDesign (design.sem N) := by
  sv_structure?
  sv_structure
  all_goals (intros; omega)

end Submission
"""

# What each step of the tutorial prints (tutorial_html), as measured on the tutorial's reference with the
# checker of this revision; `@KEY@` tokens are filled from the data (the numbers of the par design).
TUTORIAL_OUT = {
    "ppa": ("{\n"
            "  \"ppa\": {\n"
            "    ...\n"
            "    \"area_um2_sky130\": @AREA@,\n"
            "    ...\n"
            "    \"delay_ps_sky130\": @PS@,\n"
            "    ...\n"
            "  },\n"
            "  \"score\": {\n"
            "    \"area_ge\": @GE@,\n"
            "    ...\n"
            "    \"depth\": @DEPTH@,\n"
            "    ...\n"
            "}\n"),
    "unproved": ("stdout (excerpt):\n"
                 "{\"accepted\": false, \"stage\": \"unproved\", \"unproved_ok\": true,\n"
                 " \"notes\": [\"--unproved: every check that needs no proof passed (source, extract, banlist, "
                 "fourstate, design, score, postsynth); the proof stages were not run, so the design is not "
                 "accepted\"],\n"
                 " \"dev_hint\": \"cd ... && LEAN_PATH=stage/build lake env lean <YourFile>.lean ...\", ...}\n"
                 "stderr: one line as each long stage starts (check: <stage> ...), then last:\n"
                 "@HEADLINE@\n"),
    "probe_file": PROBE_FILE,
    "probe": None,                                # no listing measured for the tutorial: the text says what it shows
    "full": ("stdout (excerpt):\n"
             "{\"accepted\": true, \"stage\": \"done\", \"errors\": [],\n"
             " \"ppa\": {\"area_um2_sky130\": @AREA@, \"delay_ps_sky130\": @PS@, ...}, ...}\n"
             "stderr, last:\n"
             "@HEADLINE@\n"),
    "add": ("added @TASK@/<hash>: YOUR_HANDLE, @AREAX@ um^2, @PS@ ps (@GEX@ GE, depth @DEPTH@), @LINES@ proof lines "
            "-> my-records/@TASK@/<hash>.json\n"
            "  post-synthesis check: full mode (@VECTORS@ vectors)\n"
            "  the ranked sky130 score (A0', @PPAV@): @AREA@ um^2, @PS@ ps (area x time @AXT@ um2*ns); "
            "input drive @DRIVE@\n"
            "  ...\n"),
}


def fill_out(text, **values):
    """An expected output of the tutorial (`TUTORIAL_OUT`) with its `@KEY@` tokens filled from the data."""
    for k, v in values.items():
        text = text.replace(f"@{k}@", str(v))
    if re.search(r"@[A-Z0-9]+@", text):
        raise BuildError(f"TUTORIAL_OUT: an unfilled token in {text[:60]!r}")
    return text


def walk_reference(site, t):
    """The proved reference the tutorial's walk-through copies: content/tasks/<t>.json's `walk_through` (the stem of
    a reference whose design is par's, byte for byte, so that every number the steps print is its own; the tutorial
    names its shortest proof of that design there), else par itself."""
    src = f"{CONTENT}/tasks/{t.name}.json"
    stem = (site.content(f"tasks/{t.name}.json") or {}).get("walk_through")
    if not stem:
        return t.par
    ref = next((r for r in t.refs if r["stem"] == stem), None)
    if ref is None:
        raise BuildError(f"{src}: walk_through {stem!r} is not one of the task's proved references")
    if not t.par or ref["sha256"] != t.par["sha256"]:
        raise BuildError(f"{src}: walk_through {stem!r} is not par's design (the steps print par's numbers)")
    return ref


def tutorial_html(site, t, here):
    """The tutorial's walk-through: a first submission, every command with what it prints (`TUTORIAL_OUT`:
    the shape of each output, measured on the reference; the numbers come from the data). The pair it copies is
    `walk_reference`'s."""
    p = par_design(t)
    m = p["m"] if p else {}
    walk = walk_reference(site, t)
    stem = walk["stem"] if walk else "band"
    area, ps = m.get("area_um2"), m.get("time_ps")
    rec = next((r for r in t.ref_records if t.par and r["record_hash"] == t.par["record_hash"]), {})
    headline = check_headline(t, p)
    n = t.name

    def step(title, intro_html, cmd, out=None, out_name="what it prints"):
        body = f"<h3>{title}</h3>{intro_html}" + page.code_block(cmd, "bash", name="shell", term=True)
        if out:
            body += page.code_block(out, None, name=out_name)
        return f"<li>{body}</li>"
    out = TUTORIAL_OUT
    steps_html = "".join([
        step("Copy the reference pair",
             "<p>The task's own design and proof are a complete, accepted submission. Start from them.</p>",
             f"cp tasks/{n}/reference/{stem}.sv solution.sv\ncp tasks/{n}/reference/{stem}.lean Solution.lean\n"),
        step("Score it, no Lean",
             "<p>The golfing inner loop, about a second: the ranked area and delay of the pinned flow.</p>",
             f"python3.12 score/ppa.py solution.sv --task tasks/{n} --no-mapped\n",
             fill_out(out["ppa"], AREA=area, PS=ps, GE=m.get("area_ge"), DEPTH=m.get("depth"))),
        step("Check it without a proof",
             "<p>Every stage that needs no proof, the task's oracle included. It never accepts; it exits 0 "
             "when every stage passed, and leaves the staged design in <code>stage/</code>.</p>",
             f"python3.12 check.py tasks/{n} solution.sv --unproved --stage-dir stage\n",
             fill_out(out["unproved"], HEADLINE=headline), "what it prints (JSON on stdout, the last line on stderr)"),
        step("Probe the design",
             "<p>How the tactics read your design, before you write a proof: a probe file compiled against "
             "the staged design. It prints the design's declarations and its sites (here one, "
             "<code>plain#0</code>, the module-level <code>assign</code>) with the bits each drives and reads; "
             "the " + page.link(rel_link(here, "proving.html") + "#0-the-loop", "proving guide, section 0") +
             ", has a longer probe and its whole output for the adder.</p>",
             "cat > Probe.lean <<'EOF'\n" + out["probe_file"] + "EOF\nLEAN_PATH=stage/build lake env lean Probe.lean\n",
             out["probe"]),
        step("Check it with the proof",
             "<p>Your proof, the comparator, the kernel replay, the score and the post-synthesis check: about "
             "a minute. The post-synthesis check runs LIGHT by default (a subset of the vectors, for local "
             "feedback), so stderr also says <code>accepted, but the check was INCOMPLETE</code> … <code>rerun "
             "with --postsynth full</code>: expected, since the next step runs it in full itself.</p>",
             f"python3.12 check.py tasks/{n} solution.sv Solution.lean\n",
             fill_out(out["full"], HEADLINE=headline, AREA=area, PS=ps), "what it prints (excerpt)"),
        step("Record it",
             "<p>The whole check again, in full mode and in the OS sandbox. The reference is par, so this is "
             "a private trial: <code>--data-dir</code> keeps the record out of the board.</p>",
             f"python3.12 leaderboard/leaderboard.py add --task {n} --player YOUR_HANDLE \\\n"
             "    --sv solution.sv --lean Solution.lean --data-dir my-records\n",
             fill_out(out["add"], TASK=n, AREA=area, PS=ps, AREAX=lb.fmt_um2(round(area * 10000)),
                      GEX=lb.fmt_ge(round(m["area_ge"] * 1000)), DEPTH=m.get("depth"), LINES=walk["proof_lines"],
                      VECTORS=(rec.get("postsynth") or {}).get("vectors"), PPAV=(rec.get("ppa") or {}).get("ppa_version"),
                      DRIVE=t.drive, AXT=(f"{m['adp']:.2f}" if m.get("adp") is not None else "–"))),
    ])
    return (step0_html(site, here)
            + f'<ol class="steps walk">{steps_html}</ol>'
            + "<p><strong>Then golf.</strong> Change <code>solution.sv</code>, score each variant with "
            "<code>score/ppa.py</code>, run the check without a proof before you prove, and prove it: "
            + page.link(rel_link(here, "proving.html"), "the proving guide") + " is the reference, and "
            + page.link(rel_link(here, "tasks/add/index.html"), "the adder") + " is the first real task.</p>")


# "Start a new design": the from-scratch card of a task (decided 2026-11-05), the section of that name at the top of
# the task's README.md. The card is chosen by the task's kind, and the build checks that it names that kind's route.
# On the task page it comes after the two columns (decided 2026-11-10: the page opens with the score card, then the
# two columns from "This task"), and "How to participate" and "How to submit" link it. The page shows each part of it
# once (new_design_parts): the README's opening restates the task for a reader of the README alone, so the page
# shows none of it (the task section states it); the two commands are the first two of How to submit, with what
# they do under them (2026-11-11: How to submit is the path of a first submission, every command in it); the card
# shows the route with its steps, and the rest of the README's card, verbatim, folded.
NEW_DESIGN = "Start a new design"
NEW_DESIGN_OPTION = re.compile(r"(?<![\w-])--[a-z][a-z-]*")
NEW_DESIGN_FOLD = "proof-in-detail"                  # the id of the card's folded part (How to submit links it)
NEW_DESIGN_ROUTE = {"comb-family": ("sv_structure", "sv_interface", "sv_equations", "Library lemmas"),
                    "comb-fixed": ("sv_exhaustive", "Library lemmas"),
                    "react-family": ("satisfiedAt_of_rank", "RankModel", "mooreOut_of_combTargets",
                                     "Library lemmas"),
                    "tx-family": ("satisfiedAtV2_of_phases", "PhaseModel", "combDeps_of_ffOnly", "XSafe",
                                  "Library lemmas"),
                    "stream-family": ("satisfiedAtV2_of_phases", "PhaseModel", "combDeps_of_ffOnly", "XSafe",
                                      "Library lemmas")}
REACT_SECTION = "20-a-reactive-task-the-arbiter-reacttask"   # PROVING.md's reactive section (its anchor)


def reviewed_hash(text):
    """The fingerprint `new_design_reviewed` pins: sha256 of the text with its whitespace collapsed, 12 hex digits."""
    return hashlib.sha256(" ".join(text.split()).encode("utf-8")).hexdigest()[:12]


class NewDesignCard:
    """The README's "Start a new design" section, cut into the parts the page shows differently: `lines` (the
    section's lines), `blocks` (md.split_blocks), `fence` (the commands), `route` (the route paragraph), `shown` (the
    first block of the folded rest: the route is followed by its code block, a whole Solution.lean, and by its step
    list, both shown), `first_line` (the README line of `lines[0]`)."""

    def __init__(self, readme, lines, first_line):
        self.readme, self.lines, self.first_line = readme, lines, first_line
        self.where = f"{readme}: '## {NEW_DESIGN}'"
        self.blocks = md.split_blocks("\n".join(lines))
        bl = self.blocks
        self.fence = next((k for k, b in enumerate(bl) if b[2] == "fence"), None)
        self.route = next((k for k, b in enumerate(bl) if self.fence is not None and k > self.fence
                           and lines[b[0]].startswith("**The route")), None)
        if self.fence is None or self.route is None:
            raise BuildError(f"{self.where}: the page shows its commands (its first code block) and its route (a "
                             "paragraph starting `**The route`, after the commands); "
                             + ("no code block" if self.fence is None else "no route paragraph"))
        k = self.route + 1
        for kind in ("fence", "list"):
            if k < len(bl) and bl[k][2] == kind:
                k += 1
        self.shown = k

    def src(self, a, b):
        """The README's lines of blocks a..b-1."""
        return "\n".join(self.lines[self.blocks[a][0]:self.blocks[b - 1][1]]) if b > a else ""

    def commands(self, task):
        """The card's two commands, [(command, its trailing `# comment` or "")]: the golfing loop
        (`python3.12 score/ppa.py solution.sv --task tasks/<t>`) and the run without a proof (`python3.12 check.py
        tasks/<t> solution.sv --unproved`), in that order; How to submit shows them as its first two (one form of
        each command on the page). Any other shape of the code block fails the build."""
        a, b, _ = self.blocks[self.fence]
        body = [ln for ln in self.lines[a + 1:b - 1] if ln.strip()]
        cmds = []
        for ln in body:
            m = re.fullmatch(r"(.*?\S)(?:\s{2,}#\s*(.*))?", ln.strip())
            cmds.append((m.group(1), (m.group(2) or "").strip()))
        want = (f"python3.12 score/ppa.py solution.sv --task tasks/{task} ",
                f"python3.12 check.py tasks/{task} solution.sv --unproved")
        if (len(cmds) != 2 or not all((c + " ").startswith(w) for (c, _), w in zip(cmds, want))
                or any(q in c for c, _ in cmds for q in "'\"\\$`;|&")):
            raise BuildError(f"{self.where}: its code block holds the two commands How to submit shows first, "
                             f"one per line: {want[0].strip()} ... (the golfing loop), then {want[1]} ... (the "
                             f"check without a proof); it holds {[c for c, _ in cmds]}")
        return cmds

    def skeleton(self):
        """Where the card's Solution.lean is (a Lean code block with `theorem solution`): "shown", "folded" or None."""
        for k, (a, b, kind) in enumerate(self.blocks):
            if kind == "fence" and "theorem solution" in "\n".join(self.lines[a:b]):
                return "shown" if k < self.shown else "folded"
        return None


def new_design_card(site, t):
    """The task's NewDesignCard, or None for a task with no card. A listed task of a kind in NEW_DESIGN_ROUTE without
    one is a warning (fatal under --strict); a card that does not name its kind's route fails the build."""
    readme = f"{t.dir}/README.md"
    text = site.doc_text(readme)
    hit = [s for s in md.split_sections(text) if s[0] == 2 and s[1] == NEW_DESIGN]
    if not hit:
        if t.listing == "listed" and t.kind in NEW_DESIGN_ROUTE:
            msg = f"{readme}: no '## {NEW_DESIGN}' section (the from-scratch card of a {t.kind} task)"
            if site.strict:
                raise BuildError(msg)
            site.warn(msg)
        return None
    _, _, s0, s1 = hit[0]
    lines = text.split("\n")[s0 + 1:s1]
    missing = [w for w in NEW_DESIGN_ROUTE.get(t.kind, ()) if w not in "\n".join(lines)]
    if missing:
        raise BuildError(f"{readme}: '## {NEW_DESIGN}' of a {t.kind} task does not name {', '.join(missing)}")
    return NewDesignCard(readme, lines, s0 + 2)


def new_design_skeleton(card):
    """How to submit's pointer to the card's Solution.lean, (href, words), or None when the card has none."""
    where = card.skeleton() if card else None
    if where == "shown":
        return ("#new-design", f"the whole <code>Solution.lean</code> in {esc(NEW_DESIGN)}")
    if where == "folded":
        return (f"#{NEW_DESIGN_FOLD}", f"the skeleton in {esc(NEW_DESIGN)} (The proof in detail)")
    return None


def new_design_parts(site, t, here, slugger, card=None):
    """The README's "Start a new design" section as the page shows it: (checks, card), the HTML How to submit shows
    under its first two commands (what they do) and the card's own; ("", "") for a task with no card (`card`: the
    task's NewDesignCard, else read here).

    The card's parts, in its order, and where the page shows each (the README itself is not changed):
    1. the opening, every block before the first code block: the task restated (files, header, bans, range,
       the freedom of design), which the task section states, and the sentence that announces the commands, which
       How to submit states. Not shown; content/tasks/<t>.json `new_design_lead` (Markdown) is the card's opening
       where the task has one (a fact of the route the opening gives first);
    2. the first code block, the two commands: How to submit's first two (`NewDesignCard.commands`, read by
       `submit_commands`);
    3. what they do, the blocks up to the route: verbatim, or content/tasks/<t>.json `new_design_checks`
       where the README's text restates the task's facts (it must name every option the README's names): `checks`,
       shown under How to submit's commands;
    4. the route, the first block that starts `**The route`: verbatim (where to start, the reduction, the
       reference proof), with the code block (a whole Solution.lean) and the step list that follow it; and the
       size of every reference proof it names whose size it does not give (from the References table's count);
    5. the rest (the layout, the skeleton, the library lemmas): verbatim, in one disclosure, "The proof in
       detail" (id NEW_DESIGN_FOLD), its summary the bold lead-ins it holds.
    The page shows its own text in place of parts 1 and 3, so content/tasks/<t>.json `new_design_reviewed` pins
    what it last checked them against (`opening`, and `checks` with `new_design_checks`; reviewed_hash): a README
    edit there is a warning (fatal under --strict) that prints the new text, until the page says what it adds."""
    card = card or new_design_card(site, t)
    if card is None:
        return "", ""
    readme, where, fence, route = card.readme, card.where, card.fence, card.route

    def render(a, b):
        if b <= a:
            return ""
        return site.render_md(card.src(a, b), source=readme, here=here, first_line=card.first_line + card.blocks[a][0],
                              slugger=slugger, heading_shift=1).html

    info = site.content(f"tasks/{t.name}.json") or {}
    info_src = f"{CONTENT}/tasks/{t.name}.json"
    reviewed = info.get("new_design_reviewed") or {}

    def pin(key, text, what):
        h = reviewed_hash(text)
        if reviewed.get(key) != h:
            how = "changed since the page was last checked against it" if key in reviewed else "is not pinned"
            site.warn(f"{where}: {what} {how} (the page shows its own text there). Check that the page states every "
                      f"fact of it, then set {info_src} `new_design_reviewed.{key}` to {h!r}. The text now: "
                      f"{' '.join(text.split())!r}")

    # 1. the opening: the task section and How to submit state it; the task's own opening of the card, if any
    pin("opening", card.src(0, fence), "its opening (the text before the commands, which the task section and How "
                                       "to submit state)")
    lead_md = info.get("new_design_lead")
    parts = [site.render_md(lead_md, source=info_src, here=here, slugger=slugger).html] if lead_md else []
    # 2. the commands: How to submit's first two (checked here too, so that a card of another shape fails the build)
    card.commands(t.name)
    # 3. what the commands do, under them in How to submit
    checks_md = info.get("new_design_checks")
    if checks_md is None:
        checks = render(fence + 1, route)
    else:
        said = card.src(fence + 1, route)
        lost = sorted(set(NEW_DESIGN_OPTION.findall(said)) - set(NEW_DESIGN_OPTION.findall(checks_md)))
        if lost:
            raise BuildError(f"{info_src}: `new_design_checks` does not explain {', '.join(lost)}, which {where} "
                             "explains for its commands")
        pin("checks", said, "its text on what the two commands do")
        checks = site.render_md(checks_md, source=info_src, here=here, slugger=slugger).html
    # 4. the route: its paragraph, the whole proof when it follows as code, its steps; the size of each proof it names
    parts.append(render(route, card.shown))
    said = card.src(route, route + 1)
    sizes = []                                       # (path, code lines) of the proofs it names without a size
    for stem in dict.fromkeys(re.findall(r"reference/([\w-]+)\.lean", said)):
        ref = next((r for r in t.refs if r["stem"] == stem), None)
        if ref and not re.search(rf"(?<![\d,.]){ref['proof_lines']}(?![\d,.])", said):
            sizes.append((code(f"reference/{stem}.lean"), ref["proof_lines"]))
    if sizes and card.blocks[route + 1][2] != "fence":          # not when the whole proof is shown under it
        parts.append(f"<p>{' and '.join(p for p, _ in sizes)}, named above, "
                     f"{'is' if len(sizes) == 1 else 'are'} {' and '.join(str(n) for _, n in sizes)} code lines long.</p>")
    # 5. the rest, folded
    bl = card.blocks
    if card.shown < len(bl):
        heads = [md.render_inline(m.group(1), source=readme, line=card.first_line + b[0])
                 for b in bl[card.shown:] if b[2] == "text" for m in [re.match(r"\*\*(.+?)\*\*", card.lines[b[0]])] if m]
        summary = ('The proof in detail<span class="nd-more">' + " · ".join(heads) + "</span>")
        parts.append(page.details(summary, render(card.shown, len(bl)), cls="nd-detail", id_=NEW_DESIGN_FOLD))
    return checks, "\n".join(p for p in parts if p)


def new_design_html(site, t, here, slugger, card=None):
    """The "Start a new design" card's body as the page shows it, or "" for a task with no card: the second part of
    `new_design_parts`."""
    return new_design_parts(site, t, here, slugger, card)[1]


def participate_html(t, here, *, new_design=False):
    """How to participate, in four steps (zk.golf's list): the details are the sections they link (with
    `new_design`, the page has a "Start a new design" card, which step 2 names). Step 4 names the score and links
    the Score card, whose caption is its one definition on the page (2026-11-09)."""
    start = (f"{page.link('#new-design', NEW_DESIGN)}, below, gives the route, and " if new_design else "")
    last = (f"Beat par: an accepted design whose {page.link('#score', '<strong>score</strong>')} (area × time) is below "
            f"that of the best proved reference. The {page.link('#leaderboard', 'leaderboard')} ranks by it.")
    if t.preview:
        last = ("Golf the score. This task is a preview: submissions are not ranked yet ("
                + page.link("#leaderboard", "why") + ").")
    return page.steps([
        f"Write a circuit with the task's exact {page.link('#interface', '<strong>interface</strong>')}.",
        f"Prove in Lean 4 that it meets the {page.link('#spec', '<strong>trusted statement</strong>')}; "
        f"{start}the {page.link(rel_link(here, 'proving.html'), 'proving guide')} shows how.",
        f"Check and record it ({page.link('#submit', 'how to submit')}): the checker accepts the pair or says "
        f"which stage refused it, as it does for each design under {page.link('#does-not-count', 'what does not count')}.",
        last,
    ])


def reference_copy(t):
    """The two `cp` lines that copy par's pair (the reference under Files) to solution.sv and Solution.lean, from the
    root of svGolf, or "" for a task without par: How to submit's starting point (2026-11-11)."""
    if not t.par:
        return ""
    sv, lean = (t.par[k][len("svgolf/"):] if t.par[k].startswith("svgolf/") else t.par[k] for k in ("sv", "lean"))
    return f"cp {sv} solution.sv\ncp {lean} Solution.lean\n"


def task_page(site, t):
    here = t.page
    task = t.task
    reserved = ("numbers", "score", "statement", "interface", "spec", "closure", "participate", "leaderboard",
                "over-time", "facts", "files", "explore", "scaling", "references", "baselines", "does-not-count",
                "submit", "what-moves-the-score", "first-submission", "props-properties",
                "props-definitions", "new-design", NEW_DESIGN_FOLD,
                "step-0") + tuple(f"reject-{g}" for g, _, _ in REJECT_GROUPS)
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
    def par_files():
        if not t.par:
            return ""
        base = f"tasks/{t.name}/reference/{t.par['stem']}"
        return "".join(page.button(rel_link(here, base + ext), f"{t.par['stem']}{ext}", "quiet sm", download=True)
                       for ext in (".sv", ".lean"))
    files.append(both(t, par_files, inline=True))
    head = page.page_head(
        crumbs_html=(f'<a href="{rel_link(here, "index.html")}"><span class="back" aria-hidden="true">‹</span>Tasks</a>'
                     f" / {esc(t.name)}"),
        number=t.number, title_html=f'{esc(t.title)} <span class="task-id">{code(t.name)}</span>',
        sub_html=esc(t.subtitle) if t.subtitle else None, tags_html=" ".join(tags),
        aside_html=f'<section id="numbers">{preview_html(t) if t.preview else both(t, lambda: big_numbers(t))}</section>')
    # one line to the path of a first submission (How to submit, the second card of the left column); the tutorial's
    # walk-through follows the score card directly
    first = "" if t.listing == "tutorial" else \
        f'<p class="small first-link">First submission: {page.link("#submit", "How to submit")}</p>'
    score = page.card(both(t, lambda: score_html(site, t, here)) + first, tag="section", id_="score",
                      title_html="Score", actions_html=score_actions(t))
    statement = sec("statement", statement_html(site, t, here, slugger))
    interface = sec("interface", h("interface", "Interface") + interface_html(site, t))
    spec = sec("spec", h("spec", "The trusted statement") + spec_html(site, t, here))
    # the card is rendered after the statement, as before (the same heading ids), and shown after the two columns
    card = new_design_card(site, t)
    checks, fresh = new_design_parts(site, t, here, slugger, card)
    task_card = page.card(
        statement + interface + spec
        + h("participate", "How to participate", own_id=True) + participate_html(t, here, new_design=bool(fresh)),
        tag="article", label_html="This task",
        actions_html=page.button(rel_link(here, "proving.html"), "Proving guide", arrow=True))
    submit = page.card(submit_html(site, t, site.config.get("repo_url"), card=card if fresh else None,
                                   skeleton=new_design_skeleton(card) if fresh else None, checks=checks),
                       tag="section", id_="submit", label_html="How to submit")
    tips = score_tips_html(site, t, here)
    if tips:
        submit += page.card(tips, tag="section", id_="what-moves-the-score", title_html="What moves the score")
    walk = ""
    if t.listing == "tutorial":
        walk = page.card(tutorial_html(site, t, here), tag="section", id_="first-submission",
                         title_html="Your first submission, step by step")
    if t.preview:
        board = page.card(preview_html(t), tag="section", id_="leaderboard", title_html="Not ranked yet")
    else:
        board = page.card(both(t, lambda: leaderboard_html(site, t, here) + board_table_html(site, t, here)),
                          tag="section", id_="leaderboard", title_html="Leaderboard", flush=True,
                          actions_html=f'<span class="label">by score{pdk_text("", " · ASAP7")}</span>',
                          foot_html=(f'<div class="legend-row"><span>score: area × time, {esc(combined.UNIT)}</span>'
                                     '<span class="lg-par">par</span></div>'))
    facts = page.card(facts_html(t), id_="facts", label_html="At a glance")
    # par's design adapted from licensed code (licence_ids: what its record page's sources card says): a copy keeps
    # the notices of its header (NOTICE: a file that came with a notice keeps it)
    lic = licence_ids(read_text(t.par["sv"])) if t.par else []
    lic_html = (f'<p class="small muted">{code(t.par["stem"] + ".sv")} is adapted from licensed code '
                f'({", ".join(code(i) for i in lic)}): a design derived from it keeps the copyright and licence '
                "notices of its header.</p>" if lic else "")
    downloads = page.card('<div class="btn-row">' + "".join(files) + "</div>" + lic_html
                          + f'<p class="small muted">Every reference and baseline is under '
                            f'{page.link("#references", "proved references")} and '
                            f'{page.link("#baselines", "baselines")}.</p>',
                          id_="files", label_html="Files")
    explore = page.card(both(t, lambda: explorer_html(site, t, here)) + scaling_html(t), tag="section", id_="explore",
                        title_html="Compare the designs",
                        actions_html=f'<span class="label">{pdk_text("", "ASAP7 · ")}any two numbers · lower is '
                                     'better</span>')
    wide = [page.card(content, tag="section", id_=i, title_html=esc(title), title_id=None)
            for i, title, content in (
                ("references", "Proved references", references_html(t, here)),
                ("baselines", "Baselines", baselines_html(t, here)))]
    # "Start a new design", under the two columns (decided 2026-11-10: nothing stands between the score card and the
    # columns): the route of a design of your own, which no other part of the page gives
    start = page.card(fresh, tag="section", id_="new-design", title_html=NEW_DESIGN) if fresh else ""
    body = (head + score + walk
            + f'<div class="split"><div class="col">{task_card}{submit}</div>'
              f'<div class="col">{board}{facts}{downloads}</div></div>'
            + start + explore + "".join(wide))
    commands_once(t, body, submit_commands(t, card if fresh else None))
    site.page(here, f"{t.title} ({t.name})", body, scripts=("charts.js",), scores=True,
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

def submitted_before(a, b):
    """Whether a record submitted at `a` was submitted before one at `b` (leaderboard.py's DATE_RE: a date, with a
    time of day only if the record gives one). Two records of the same day are ordered only when both give a time;
    otherwise neither is before the other (never by hash)."""
    if len(a) > 10 and len(b) > 10:
        return a < b
    return a[:10] < b[:10]


def same_day_records(rec, records):
    """The task's other records that `submitted_before` orders neither way against `rec` (same day, no time)."""
    a = rec["submitted_at"]
    return [r for r in records if r["record_hash"] != rec["record_hash"]
            and not submitted_before(r["submitted_at"], a) and not submitted_before(a, r["submitted_at"])]


def previous_frontier_record(rec, records):
    """The record this one was up against: the best (row_key-first) record
    of the Pareto frontier of the task's records submitted before it (`submitted_before`)."""
    earlier = [r for r in records if submitted_before(r["submitted_at"], rec["submitted_at"])]
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


# ---------------------------------------------------------------------------
# detail pages (a record's, or a proved reference's without a record): the overview (Area,
# Performance and Score cards, standing.py); the sources; two columns, the netlist card (the schematic,
# the critical-path data of site/schematics/ (gen_schematics.py) and the cells, as tabs) beside the
# record's or the reference's facts; the area-time plot, reproduce (the order: the owner, 2026-11-09)
# ---------------------------------------------------------------------------

SCHEMATICS = "svgolf/site/schematics"
NETLISTSVG_LICENCE = "LICENSE-netlistsvg.txt"
AXIS_WORDS = {"area": ("smaller", "larger"), "time": ("faster", "slower"), "score": ("better", "worse")}


def reference_page(t, ref):
    """The site path of a proved reference's detail page: its record's page when it was recorded. A preview has no
    detail pages (they are the ranked numbers' pages: the cards, par, the board, and the schematic data and the
    reproduce command of site/gen_schematics.py's combinational flow), so its references are their rows of the
    task page."""
    if ref.get("record_hash"):
        return f"tasks/{t.name}/records/{ref['record_hash']}.html"
    if t.preview:
        return f"{t.page}#ref-{ref['stem']}"
    return f"tasks/{t.name}/reference/{ref['stem']}.html"


def design_page(t, d):
    """The site path of a design's detail page (a record's, a reference's), or None (a baseline: its row)."""
    if d["kind"] == "record":
        return f"tasks/{t.name}/records/{d['id']}.html"
    if d["kind"] == "reference":
        ref = next((r for r in t.refs if r["stem"] == d["stem"]), None)
        return reference_page(t, ref) if ref else None
    return None


def design_target(t, d):
    """Where a design's mark or name links, as a site path: its detail page, else its row on the task page."""
    return design_page(t, d) or f"{t.page}#baseline-{d['stem']}"


def thin(v):
    """An integer in thin-space groups ('37 984')."""
    return f"{v:,}".replace(",", " ")


def um2_text(e4, digits=2, pdk="sky130"):
    """An area in the integer unit of `pdk`'s columns (1e-4 µm² on sky130, 1e-5 µm² on ASAP7, whose areas get three
    decimals) as µm² text, thin-space groups."""
    digits = 3 if pdk == "asap7" else digits
    return f"{e4 / combined.AREA_SCALE[pdk]:,.{digits}f}".replace(",", " ")


def um2_exact(v, pdk="sky130"):
    """An area in `pdk`'s integer unit as its exact decimal text ('460.4416', on ASAP7 '6.99840')."""
    return lb.fmt_um2_e5(v) if pdk == "asap7" else lb.fmt_um2(v)


def signed_pct(rel):
    if rel == 0:
        return "±0%"
    return ("+" if rel > 0 else "−") + f"{abs(rel) * 100:.1f}%"


def counted(n, noun):
    """'1 buffer', '0 buffers', '1 450 cells' (thin-space groups)."""
    return f"{thin(n)} {noun}{'' if n == 1 else 's'}"


def ordinal(n):
    return f"{n}{'th' if 10 <= n % 100 <= 20 else {1: 'st', 2: 'nd', 3: 'rd'}.get(n % 10, 'th')}"


def plotted(t):
    """The task's designs with both ranked numbers (the view's area and time) at the scoring point."""
    return [d for d in t.designs if "area_um2" in d["m"] and "time_ps" in d["m"]]


def st_point(d, pdk="sky130"):
    """A design as standing.py takes it: exact integers (area in `pdk`'s unit, 1e-4 µm² on sky130, 1e-5 µm² on
    ASAP7; time in ps)."""
    return {"id": d["id"], "kind": d["kind"], "player": d.get("player"),
            "area": combined.area_int(d["m"]["area_um2"], pdk), "time": d["m"]["time_ps"]}


class Subject:
    """What one detail page is about: the design (`d`, a dict of `task_designs`, or None when it has no ranked
    numbers), its record (`rec`) or reference (`ref`), the design and proof files, and the weighing the page shows
    (`ppa`: the record's own block, else the scored block of the design's site/schematics data)."""

    def __init__(self, t, here, *, rec=None, ref=None):
        self.t, self.here, self.rec, self.ref = t, here, rec, ref
        if rec is not None:
            base = f"svgolf/leaderboard/data/{t.name}/{rec['record_hash']}"
            self.sv_rel, self.lean_rel = base + ".sv", base + ".lean"
            self.sv_sha = rec["files"]["sv"]["sha256"]
            self.d = next((d for d in t.designs if d["id"] == rec["record_hash"]), None)
            if self.d is None and ref is not None:
                self.d = design_of(t, "reference", ref["stem"])
        else:
            self.sv_rel, self.lean_rel, self.sv_sha = ref["sv"], ref["lean"], ref["sha256"]
            self.d = design_of(t, "reference", ref["stem"])
        if self.d is not None and not ("area_um2" in self.d["m"] and "time_ps" in self.d["m"]):
            self.d = None
        self.sch, self.svg, self.sch_note = None, None, None
        self.ppa = rec["ppa"] if rec is not None and isinstance(rec.get("ppa"), dict) and rec["ppa"].get("available") \
            else None

    @property
    def is_ref(self):
        return self.ref is not None


def load_schematic(site, s):
    """The site/schematics data of the subject's design (gen_schematics.py), checked against the numbers the page
    shows: used only when its scored area and delay are the page's and its weighing is the current ppa_version.
    A missing or stale file leaves the sections it feeds saying so, with a warning (fatal under --strict)."""
    key = s.sv_sha[:16]
    rel = f"{SCHEMATICS}/{s.t.name}/{key}.json"
    if not os.path.isfile(repo_file(rel)):
        s.sch_note = "not computed yet: site/gen_schematics.py has not been run since this design was added"
        site.warn(f"{s.t.name}: no {rel} for {s.sv_rel}: run site/gen_schematics.py")
        return
    data = json.loads(read_text(rel))
    sc = data.get("scored") or {}
    want = None
    if s.d is not None:
        m = s.d["m"]
        # the file's delay is the flow's: on a latency kind the register-to-register period, which the ranked time
        # multiplies by the cycles
        want = (combined.e4um2(m["area_um2"]),
                m["period_ps"] if metrics.has_latency(s.t.task) and "period_ps" in m else m["time_ps"])
    stale = []
    if data.get("sv_sha256") != s.sv_sha:
        stale.append("another design file")
    if sc.get("ppa_version") != (site.ppa_identity or {}).get("ppa_version"):
        stale.append(f"weighed under {sc.get('ppa_version')}")
    if want and (sc.get("area_e4um2_sky130"), sc.get("delay_ps_sky130")) != want:
        stale.append(f"its scored numbers ({sc.get('area_e4um2_sky130')}, {sc.get('delay_ps_sky130')} ps) are not the "
                     f"page's ({want[0]}, {want[1]} ps)")
    if stale:
        s.sch_note = "stale: " + "; ".join(stale) + " (site/gen_schematics.py regenerates it)"
        site.warn(f"{s.t.name}: {rel} is stale for {s.sv_rel}: " + "; ".join(stale))
        return
    s.sch = data
    if s.ppa is None and want:
        s.ppa = sc                                   # the same numbers, with the histogram and the path
    disp = data.get("display") or {}
    if disp.get("drawn"):
        svg_rel = f"{SCHEMATICS}/{s.t.name}/{key}.svg"
        raw = read_bytes(svg_rel)
        if sha256(raw) != disp.get("svg_sha256"):
            site.warn(f"{s.t.name}: {svg_rel} is not the drawing {rel} records")
            return
        s.svg = raw.decode("utf-8")
        if schematic_file(s) not in site.files:          # the file on its own (pages of one design share it)
            site.copy(schematic_file(s), svg_rel)
        if schematic_licence(s) not in site.files:       # netlistsvg's MIT notice, beside the drawings it covers
            site.copy(schematic_licence(s), f"{SCHEMATICS}/{NETLISTSVG_LICENCE}")


# -- the dashboard --------------------------------------------------------

def other_players(n):
    return f"{n} other player{'' if n == 1 else 's'}"


def grouped(text):
    """A decimal's whole part in thin-space groups, as every other number of the overview ('7 961.3856')."""
    whole, dot, frac = text.partition(".")
    return (thin(int(whole)) if whole.isdigit() else whole) + dot + frac


def big_html(number_text, unit_html):
    """A card's big number: its digit groups' narrow spaces set in the text face (the monospace face draws each a
    whole figure wide, so '2 479' read as two numbers), then the unit."""
    groups = esc(number_text).replace(" ", '<span class="g"> </span>')
    return f'{groups}<span class="unit">{unit_html}</span>'


def meter(ax, segs):
    """A beats/matches bar: one segment per class, in proportion (drawn only when there is a field)."""
    cls = {"beaten": "m-beat", "matched": "m-tie", "level": "m-tie", "tradeoff": "m-trade", "behind": "m-behind",
           "ahead": "m-behind"}
    words = {"beaten": "beaten", "matched": "equal", "behind": "behind", "level": "level", "tradeoff": "trade off",
             "ahead": "ahead"}
    label = ", ".join(f"{words[k]} {ax[k]}" for k in segs) + f" of {other_players(ax['n'])}"
    parts = "".join(f'<span class="{cls[k]}" style="flex-grow:{ax[k]}"></span>' for k in segs if ax[k])
    return f'<div class="meter" role="img" aria-label="{esc(label)}">{parts}</div>'


def beats_html(ax):
    """An axis's beats/matches line over the field; none for an empty field (said once, under the cards)."""
    if ax["n"] == 0:
        return ""
    return (meter(ax, ("beaten", "matched", "behind"))
            + f'<p class="beats"><strong>Beats {esc(ax["beats_text"])}</strong> <span class="muted">· matches '
              f'{esc(ax["matches_text"])}</span></p><p class="fine">{ax["beaten"]} of {other_players(ax["n"])} '
              f'beaten, {ax["matched"]} equal.</p>')


def vs_par_row(s, st, axis, fmt_v, par):
    """The card's "vs par" row: the signed difference and its word, and under them, quietly, par's name (a link to
    its page) and its own number: two lines on every card, where par's name used to wrap onto a line of its own."""
    if s.d is not None and s.d["par"]:
        return ("vs par", "this design <strong>is par</strong>")
    if par is None or st["vs_par"] is None:
        return ("vs par", f'<span class="muted">no par with {PDK_A[s.t.pdk]} score</span>')
    vp = st["vs_par"][axis]
    good, bad = AXIS_WORDS[axis]
    word = "equal" if vp["delta"] == 0 else (good if vp["delta"] < 0 else bad)
    pd = par_design(s.t)
    name = esc(par["id"].split("/", 1)[-1])
    if pd is not None and pd["id"] == par["id"]:
        name = page.link(rel_link(s.here, design_target(s.t, pd)), name)
    return ("vs par", f'<strong>{esc(signed_pct(vp["rel"]))}</strong> {word}'
                      f'<span class="mpar">{name} · {esc(fmt_v(standing.value(par, axis)))}</span>')


def among_row(st, axis):
    """The card's "on this page" row: the design's place among the designs of the page's area-time plot (what they
    are is said once, under the cards: not a ranking), the designs a link to the plot further down. None when the
    plot has this design alone: the note says it once, where each card said "the only design with sky130 numbers"."""
    a = st["among"][axis]
    if a["of"] == 1:
        return None
    best = {"area": "smallest", "time": "fastest", "score": "best"}[axis]
    place = best if a["place"] == 1 and not a["tied"] else ordinal(a["place"])
    tied = f' <span class="muted">(tied with {a["tied"]})</span>' if a["tied"] else ""
    of = page.link("#area-time", f"{a['of']} designs")
    return ("on this page", f"<strong>{esc(place)}</strong> of {of}{tied}")


def rows_html(rows, cls="mrows"):
    """A card's rows: a quiet term beside its value (plain text, the values' figures tabular); a None row is left
    out."""
    return f'<dl class="{cls}">' + "".join(f"<dt>{esc(r[0])}</dt><dd>{r[1]}</dd>" for r in rows if r) + "</dl>"


def tag(text):
    """A secondary number's status beside it (extra, derived, research): shown, never ranked."""
    return f' <span class="tag">{esc(text)}</span>'


def board_rows(s, st, designs):
    """The Score card's rows: its place on the board (or par's), and on the area-time plot's Pareto front."""
    t, d = s.t, s.d
    if d["kind"] == "reference":
        where = ("<strong>par</strong>, the bar to beat: never ranked" if d["par"]
                 else "a proved reference, shown with par: never ranked")
    else:
        row = next((r for r in t.ranked() if r["record_hash"] == d["id"]), None)
        pos = st["position"]
        where = (f"layer {row['layer']}, rank {pos['rank']} of {pos['of']} by score" if row and pos else "not ranked")
    if len(designs) <= 1:
        return [("board", where)]       # alone on the plot, "on the front" says nothing (the note says it is alone)
    others = [o for o in designs if o["id"] != d["id"] and standing.dominates(st_point(o), st_point(d))]
    front = (page.link("#area-time", "on the front") if not others else
             f'dominated {page.link("#area-time", "on this page")} by '
             + and_list([page.link(rel_link(s.here, design_target(t, o)), esc(o["name"]))
                         for o in sorted(others, key=lambda o: o["id"])]))
    return [("board", where), ("Pareto", front)]          # the front of the designs on this page (the plot's, linked)


def board_field_html(st):
    """The board's standing against the field: beaten, level, trade off, ahead (none for an empty field), across
    the card under its rows, as the beats/matches line is above them. The four words are defined once, in the note
    under the cards (a definition in brackets after "0 beaten" read as a claim)."""
    b = st["board"]
    if b["n"] == 0:
        return ""
    return ('<div class="mboard">' + meter(b, ("beaten", "level", "tradeoff", "ahead"))
            + f'<p class="fine">On the board, of {other_players(b["n"])}: {b["beaten"]} beaten, {b["level"]} level, '
              f'{b["tradeoff"]} trade off, {b["ahead"]} ahead.</p></div>')


def critical_words(p):
    """Where a critical path ends, as words: the output bit, or on a clocked netlist the net a flip-flop samples
    at its D input (ppa.py names that endpoint `D:<net>`), and the edge."""
    c = (p or {}).get("critical") or {}
    if not c.get("output"):
        return ""
    edge = {"r": "rising", "f": "falling"}.get(c.get("edge"), "")
    if c["output"].startswith("D:"):
        return f"the flip-flop input {code(c['output'][2:])} {edge}".strip()
    return f"{code(c['output'])} {edge}".strip()


def drive_words(p):
    setup = (p or {}).get("setup") or {}
    drive = setup.get("input_drive") or ""
    return (code(drive.replace("sky130_fd_sc_hd__", "").replace(metrics.ASAP7_SUFFIX, "")) if drive
            else "an ideal ramp")


def mcard(key, label_html, big_html, sub_html, field_html, rows, facts=(), cls="", after_html=""):
    """One card of the overview: a label, the big number, one line under it, the field's line (when there is a
    field), then the body: the standing rows (and `after_html` under them: the board's standing against the field)
    and the secondary numbers under a rule. Every card has the same five parts, empty or not, so that side by side
    (style.css, a subgrid) each part starts level with its neighbours' and the rules line up."""
    c = f"mcard {cls}".strip()
    return (f'<section class="{c}" aria-labelledby="h-{key}"><h3 class="label" id="h-{key}">{label_html}</h3>'
            f'<p class="big">{big_html}</p><p class="sub">{sub_html}</p><div class="mfield">{field_html}</div>'
            f'<div class="mbody">{rows_html(rows)}{after_html}'
            + (rows_html(facts, "mrows mfacts") if facts else "") + "</div></section>")


def dashboard_html(s, st, par, designs):
    """The overview: three cards, Area, Performance (time), Score (area × time), each with its vs-par and
    on-this-page rows and its secondary numbers, and with a field its beats/matches line; then one note, said once
    for the three: that the field is empty (when it is), and folded under it the field's definition, what "on this
    page" counts, how the numbers are measured and which are ranked (it stood as six lines of fine print under the
    cards)."""
    t, d, p = s.t, s.d, s.ppa or {}
    m = d["m"]
    pdk = t.pdk
    area_e4, time = combined.area_int(m["area_um2"], pdk), m["time_ps"]     # 1e-5 µm² in the ASAP7 view
    field = st["field_players"] > 0
    cells = (page.link("#cells", esc(thin(p["cells_sky130"]))) if "cells_sky130" in p
             else esc(thin(p["cells_asap7"])) if "cells_asap7" in p else '<span class="muted">–</span>')
    area_facts = [("cells", cells), ("flops", esc(str(p.get("flops") or m.get("ffs") or 0)))]
    if p.get("repair"):
        rp = p["repair"]
        area_facts.append(("repair", esc(f"{counted(rp['buffers'], 'buffer')}, {counted(rp['tie_cells'], 'tie cell')}")))
    area_facts.append(("GE", esc(grouped(compact_ge(round(m["area_ge"] * 1000)))) + tag("extra")))
    mapped = (s.rec or {}).get("ppa", {}).get("mapped") if s.rec and pdk == "sky130" else None
    if isinstance(mapped, dict) and mapped.get("available"):
        area_facts.append(("A1′", esc(um2_text(mapped["area_e4um2_sky130_mapped_v1"])) + " µm²" + tag("research")))
    clocked = "cycles" in m and "period_ps" in m
    sub_time = ("the register-to-register period, one decision per cycle: the latest arrival at an output, or at a "
                "flip-flop's D plus setup, ideal clock" if clocked and not metrics.has_latency(t.task) else
                f"{counted(m['cycles'], 'cycle')} × {thin(m['period_ps'])} ps; the period is the latest arrival at an "
                "output, or at a flip-flop's D plus setup, ideal clock" if clocked else
                f"the delay: the latest output arrival, {critical_words(p) or 'at an output'}" if pdk == "sky130" else
                "the delay: the latest output arrival")
    time_facts = [("Fmax-eq.", esc(f"{1e6 / time:.1f}") + " MHz" + tag("derived"))]
    if (p.get("critical") or {}).get("cells") is not None:
        time_facts.append(("critical path", page.link("#critical-path", counted(p["critical"]["cells"], "cell"))))
    time_facts.append(("unit depth", esc(str(p.get("unit_depth", m.get("depth")))) + tag("extra")))
    if isinstance(mapped, dict) and mapped.get("available"):
        time_facts.append(("A1′", esc(thin(mapped["mapped_delay_sky130_v1"])) + " ps" + tag("research")))
    ex = area_e4 * time
    exact = grouped(um2_exact(area_e4, pdk))       # grouped as the big number above it and the time beside it
    area_card = mcard(
        "area", "Area", big_html(um2_text(area_e4, pdk=pdk), "µm²"), f"{esc(exact)} µm² exactly",
        beats_html(st["axes"]["area"]),
        [vs_par_row(s, st, "area", lambda v: f"{um2_text(v, pdk=pdk)} µm²", par), among_row(st, "area")], area_facts)
    time_card = mcard(
        "time", "Performance · time", big_html(thin(time), "ps"), sub_time,
        beats_html(st["axes"]["time"]),
        [vs_par_row(s, st, "time", lambda v: f"{thin(v)} ps", par), among_row(st, "time")], time_facts)
    score_card = mcard(
        "score", "Score · area × time", big_html(combined.fmt(combined.um2ns(ex, pdk)), nocase(esc(combined.UNIT))),
        f"{esc(exact)} µm² × {esc(thin(time))} ps",
        beats_html(st["axes"]["score"]),
        [vs_par_row(s, st, "score", lambda v: f"{combined.fmt(combined.um2ns(v, pdk))} {combined.UNIT}", par),
         among_row(st, "score")] + board_rows(s, st, designs), cls="score-card",
        after_html=board_field_html(st))
    n_p, n_r = st["field_players"], st["field_records"]
    empty = (f'<p class="fine">No other player has a ranked record on {code(t.name)} yet: the beats and matches '
             "lines come with the first one.</p>" if not field else "")
    nref = sum(1 for x in designs if x["kind"] == "reference")
    nrec = sum(1 for x in designs if x["kind"] == "record")
    nbase = len(designs) - nref - nrec
    kinds = and_list([f"{n} {w}{'' if n == 1 else 's'}" for n, w in ((nref, "reference"), (nrec, "submission"),
                                                                     (nbase, "baseline")) if n])
    among = (f"“On this page” and “Pareto” compare with the {len(designs)} designs of the area-time plot "
             f"({esc(kinds)}): not a ranking." if len(designs) > 1 else
             f"This design is the only one with {PDK_NAME[pdk]} numbers on this page, so the cards have no “on this page” or "
             "“Pareto” row.")
    counts = ("each player counts once, at their best, and ties are exact at the recorded unit; " if field else "")
    field_note = (f"The field is the ranked records of {code(t.name)}'s other players at this "
                  f"revision ({n_p} player{'' if n_p == 1 else 's'}, {n_r} record{'' if n_r == 1 else 's'}), never "
                  f"the references, the baselines or a rejected design; {counts}advisory, recomputed at every build, "
                  "never stored in a record and never used by the ranking.")
    board_words = ("On the board, another player is beaten when this design dominates every record of theirs, level "
                   "when none of theirs is better and one is identical (the rest dominated), ahead when a record of "
                   "theirs dominates this design, and a trade off otherwise (one of theirs better on one axis, worse "
                   "on the other)." if st["board"]["n"] else "")
    measured = ("Area: sky130 A0′, the repaired netlist."
                + (f" Time: NLDM, inputs driven by {drive_words(p)}, 10 fF per output bit, no wires." if not clocked
                   else "")) if pdk == "sky130" else (
        "Area: ASAP7 A0′ (asap7_a0_v1), the same scored netlist, each gate its least-area ASAP7 build, repaired by "
        "buffering." + (f" Time: NLDM, inputs driven by {drive_words(p)}, 2.5 fF per output bit, no wires; a table "
                        "read below its grid is read at its floor." if not clocked else "")
        + " " + asap7_words(s.here, short=True))
    ranked = (("Area, time and score are ranked (the leaderboard orders by the score)" if pdk == "sky130" else
               "Area, time and score order this view's board (by the score); the records' ranked score is sky130's, "
               "the default view")
              + "; a number tagged extra, derived or research is shown, never ranked. Fmax-equivalent = 10⁶ / time "
              "in ps, for comparison with sites that quote Fmax.")
    more = page.details("how these numbers are measured and compared",
                        "".join(f'<p class="fine">{x}</p>' for x in (measured, ranked, field_note, board_words, among)
                                if x),
                        cls="reveal")
    note = f'<div class="dash-note">{empty}{more}</div>'
    return f'<div class="dash">{area_card}{time_card}{score_card}</div>{note}'


# -- the area-time plot ---------------------------------------------------

def area_time_html(s, par):
    """This design among the task's designs: sky130 area against the ranked time, the front of the entries, par's
    score curve, fitted to the cluster (standing.fit_axis), with an "all designs" view when that hides any (charts.js
    switches); the same numbers in a table under it."""
    t, here = s.t, s.here
    designs = plotted(t)
    pts = []
    for d in designs:
        target = design_target(t, d)
        tip = tip_lines(d, [m for m in task_metrics(t) if m.key in ("adp", "area_um2", "time_ps")])
        pts.append({"id": d["id"], "kind": d["kind"], "x": d["m"]["area_um2"], "y": d["m"]["time_ps"],
                    "banned": d["banned"], "tip": (["this design"] if d is s.d else []) + tip,
                    "href": None if d is s.d else rel_link(here, target), "label": d["name"], "attrs": {"id": d["id"]}})
    entries_ = [p for p in pts if p["kind"] != "baseline"]
    front = pareto_ids(entries_)
    keep_x = [p["x"] for p in pts if p["id"] in front or p["id"] == s.d["id"] or (par and p["id"] == par["id"])]
    keep_y = [p["y"] for p in pts if p["id"] in front or p["id"] == s.d["id"] or (par and p["id"] == par["id"])]
    xs, ys = [p["x"] for p in pts], [p["y"] for p in pts]
    fit = standing.fit_axis(xs, keep_x) + standing.fit_axis(ys, keep_y)
    every = standing.fit_axis(xs, xs) + standing.fit_axis(ys, ys)
    pdk, lib = t.pdk, PDK_NAME[t.pdk]
    par_curve = ({"id": par["id"], "score": par["area"] / combined.AREA_SCALE[pdk] * par["time"],
                  "label": f"par's score: area × time = {combined.fmt(combined.um2ns(standing.score(par), pdk))} "
                           f"{combined.UNIT}"}
                 if par else None)
    views = [("fit", fit)] + ([("all", every)] if every != fit else [])

    def chart(view, compact):
        return svgplot.area_time_chart(pts, subject=s.d["id"], view=view, x_label=f"{lib} area (µm²)",
                                       y_label="time (ps)", front=front, par=par_curve, compact=compact,
                                       title=f"{t.name}: this design's {lib} area against time, among the task's designs")
    variants = "".join(f'<div class="chart-variant" data-view="{v}" data-size="{"compact" if c else "wide"}"'
                       f'{" hidden" if v == "all" else ""}>{chart(view, c)}</div>'
                       for v, view in views for c in (False, True))
    edges, beyond = standing.beyond([(p["x"], p["y"]) for p in pts], fit)
    tools = ""
    if len(views) > 1:
        tools = ('<div class="chart-tools" data-view-toggle hidden>'
                 + page.seg(["Fit to cluster", "All designs"], 0, label_text="the plot's view") + "</div>")
    kinds = {p["kind"] for p in pts if p["kind"] != "baseline" or not p["banned"]} \
        | ({"banned"} if any(p["banned"] for p in pts) else set())
    legend = legend_html(kinds, front="the Pareto front of the entries")
    extra = ('<ul class="legend"><li><svg class="legend-icon" viewBox="0 0 20 20" width="20" height="20" aria-hidden="true">'
             '<circle class="halo" cx="10" cy="10" r="8"/></svg>this design</li>'
             + ('<li><svg class="legend-icon" viewBox="0 0 20 20" width="20" height="20" aria-hidden="true">'
                '<path class="iso" d="M3 3Q6 15 18 17"/></svg><span>par\'s score: area × time = '   # one flex item
                f'{esc(combined.fmt(combined.um2ns(standing.score(par), pdk)))}\u00a0{nocase(esc(combined.UNIT))}</span>'
                '</li>' if par else "")
             + "</ul>")
    fitted = (f"Fitted to the cluster: {beyond} design{'' if beyond == 1 else 's'} beyond the view, counted at its "
              "edge (◂ ▸ ▴ ▾); “All designs” shows them." if beyond else
              "Every design is in view." if len(pts) < standing.MIN_FIT else
              "Fitted to the cluster; every design is in view.")
    rows = []
    for d in sorted(designs, key=score_key):
        name = code(d["name"]) if d["kind"] != "record" else esc(d["name"])
        link = name if d is s.d else page.link(rel_link(here, design_target(t, d)), name)
        rows.append(page.Row([link + " " + esc("· this design" if d is s.d else ""), esc(kind_text(d)),
                              esc(um2_text(combined.area_int(d["m"]["area_um2"], pdk), pdk=pdk)),
                              esc(thin(d["m"]["time_ps"])),
                              esc(combined.fmt(d["m"].get("adp")))], cls="is-subject" if d is s.d else None))
    table = page.table(heads("design", "kind", "area (µm²)", "time (ps)", f"score ({combined.UNIT})"), rows,
                       numeric=(2, 3, 4))
    return (f'<div class="chart-slot" data-hook="area-time">{tools}'
            f'<figure class="chart-figure"><div class="chart-box" data-area-time>{variants}</div>{legend}{extra}'
            f"<figcaption>{lib} area (x) against {'the ranked' if pdk == 'sky130' else 'the ' + lib} time (y); lower "
            "left is better on both. The step line is "
            "the Pareto front of the entries (the proved references and the players' ranked records); a design under "
            "par's score curve has a better score than par. Baselines are drawn for scale: scored, never proved. "
            f"{fitted}</figcaption></figure></div>"
            + page.details("the designs as numbers, by score", table))


# -- the schematic, the critical path, the cells --------------------------

def point_words(params, t=None):
    """Parameters as words, in the task's own order when `t` is given ('W = 3, P = 3')."""
    if t is not None:
        params = {**{k: params[k] for k in t.point if k in params}, **params}
    return ", ".join(f"{k} = {v}" for k, v in params.items()) or "its one fixed size"


def schematic_html(s):
    t = s.t
    if s.sch is None:
        return f'<p class="empty">The schematic is {esc(s.sch_note or "not computed yet")}.</p>'
    disp, sc = s.sch["display"], s.sch["scored"]
    at, scored_at = point_words(disp["params"], t), point_words(sc["params"], t)
    same = disp["params"] == sc["params"]
    if not disp.get("drawn"):
        return f'<p class="empty">No schematic: {esc(disp.get("reason", "not drawn"))}.</p>'
    c = disp.get("critical") or {}
    path_cells = c.get("cells")
    # the lead says what is drawn, in a line or two; how it is drawn goes under the drawing, in the fine print
    if same:
        lead = (f"The repaired A0′ netlist that the score weighs: {counted(disp['cells_sky130'], 'cell')}. "
                f"{code(t.name)} has one fixed size, so there is no smaller instance to draw.")
        how = ""
    else:
        lead = (f"<strong>Drawn at {esc(at)}, a display instance; scored at {esc(scored_at)}.</strong> Only this "
                "drawing and the notes under it are at the smaller size: the critical path, the cells and every other "
                "number on this page are the scored netlist's.")
        how = (f"It is the same design through the same pinned flow at a smaller size ({code('ppa.py --param')}), so "
               f"that what it does can be seen: {counted(disp['cells_sky130'], 'cell')} here, "
               f"{thin(sc['cells_sky130'])} at the scoring point. ")
    if disp["drawn"] == "critical":
        how += (f"The drawing is its critical path ({counted(disp['drawn_cells'], 'cell')}, ending at "
                f"{critical_words(disp)}, {thin(disp['delay_ps_sky130'])} ps), every cell of it, and each net that "
                "enters or leaves the path drawn as a port named after the net: the whole netlist at this size is a "
                "tangle of wires. The path's own nets are in the accent colour. ")
    elif sc.get("sequential"):
        how += (f"The register-to-register critical path at {esc(at)} ({counted(path_cells, 'cell')}, ending at "
                f"{critical_words(disp)}; a period of {thin(disp['delay_ps_sky130'])} ps there) is in the accent "
                "colour. ")
    else:
        how += (f"The critical path at {esc(at)} ({counted(path_cells, 'cell')}, ending at {critical_words(disp)}, "
                f"{thin(disp['delay_ps_sky130'])} ps there) is in the accent colour. ")
    how += ("Drawn by netlistsvg with svGolf's sky130 skin (derived from netlistsvg's default skin, as the drawing "
            "is: MIT licence, Copyright (c) 2016 Neil Turley, "
            + page.link(rel_link(s.here, schematic_licence(s)), "the notice") + "): one symbol per cell function, "
            "the cell above it, the "
            "instance on hover; " + code("nor2b") + " and " + code("nand2b") + " are drawn with the bubble on their "
            "inverted input. The cells of the path are listed under " + page.link("#critical-path", "Critical path")
            + ", each a link to the cell here.")
    tools = ('<div class="sch-tools" data-schematic-tools hidden>'
             '<button type="button" data-zoom="out" aria-label="Zoom out">−</button>'
             '<button type="button" data-zoom="in" aria-label="Zoom in">+</button>'
             '<button type="button" data-zoom="fit">Fit</button>'
             '<button type="button" data-zoom="one" aria-label="Actual size">1:1</button>'
             + ('<label class="log-toggle"><input type="checkbox" data-crit checked> the critical path</label>'
                if ' class="crit"' in s.svg or ' crit"' in s.svg else '')
             + '<span class="sch-find"><input type="search" data-find aria-label="Find a cell by instance or type" '
               'placeholder="find a cell: _12_, xor2" autocomplete="off" spellcheck="false">'
               '<span class="fine" data-find-count aria-live="polite"></span></span>'
             + "</div>")
    numbers = ("" if same else f" There (measured, not ranked): {esc(um2_text(disp['area_e4um2_sky130']))} µm², "
               f"{thin(disp['delay_ps_sky130'])} ps.")
    own = page.link(rel_link(s.here, schematic_file(s)), "the drawing on its own")
    return (f"<p>{lead}</p>{tools}"
            f'<div class="sch-box" data-schematic tabindex="0" role="group" aria-label="schematic, scrollable">'
            f"{schematic_svg(s)}</div>"
            f'<p class="fine">{how}</p>'
            f'<p class="fine">The netlist at {esc(at)}: {thin(disp["cells_sky130"])} cells, '
            + ", ".join(f"{n} {code(k)}" for k, n in sorted(disp["cell_hist_sky130"].items(), key=lambda kv: (-kv[1], kv[0])))
            + (f"; {thin(disp['drawn_cells'])} drawn" if disp["drawn"] == "critical" else "") + f".{numbers} "
            f"Open {own} (SVG, {esc(kb_text(len(s.svg.encode('utf-8'))))}) to pan and zoom it with the browser's own "
            "controls.</p>")


def schematic_file(s):
    """The site path of the subject's drawing as a file of its own (one per design file; pages share it)."""
    return f"tasks/{s.t.name}/schematics/{s.sv_sha[:16]}.svg"


def schematic_licence(s):
    """The site path of netlistsvg's licence notice, beside the task's drawings: the skin they are drawn with is
    derived from netlistsvg's default skin (MIT), and so are they (NOTICE)."""
    return f"tasks/{s.t.name}/schematics/{NETLISTSVG_LICENCE}"


def schematic_svg(s):
    """The drawing as the page inlines it: each cell's group gets the id `sch-<instance>`, the target of the
    critical-path links (the committed file stays as gen_schematics.py wrote it)."""
    return re.sub(r'<g ([^>]*?)data-inst="([^"]+)"', r'<g \1id="sch-\2" data-inst="\2"', s.svg)


def kb_text(n):
    return f"{n / 1000:,.1f} KB".replace(",", " ")


def sch_link(s, inst, label_html):
    """A link to the cell `inst` in the page's schematic, or the label alone when the drawing lacks it."""
    if s.svg is not None and f'data-inst="{inst}"' in s.svg:
        return f'<a class="sch-link" href="#sch-{esc(inst)}">{label_html}</a>'
    return label_html


def drawn_path_html(s):
    """The display instance's critical path, cell by cell, each a link to the cell in the schematic (drawn at a
    smaller size than the scoring point, so the scored table's instances are not in the drawing)."""
    disp = s.sch["display"]
    path = disp.get("path") or []
    if not path:
        return ""
    items = []
    for k, n in enumerate(path):
        if n.get("inst"):
            items.append("<li>" + sch_link(s, n["inst"], f'{code(n["inst"])} <span class="muted">{esc(n["cell"] or "")}</span>')
                         + "</li>")
        elif k == 0:
            items.append(f"<li>{code(n['net'])}</li>")
    end = (disp.get("critical") or {}).get("output") or path[-1]["net"]
    items.append(f"<li>{code(end[2:])} <span class=\"muted\">flip-flop D</span></li>" if end.startswith("D:") else
                 f"<li>{code(end)}</li>")
    at = point_words(disp["params"], s.t)
    there = (f"a period of {thin(disp['delay_ps_sky130'])} ps there" if s.sch["scored"].get("sequential") else
             f"{thin(disp['delay_ps_sky130'])} ps there")
    return (f"<p>In the schematic, drawn at {esc(at)}, the critical path is "
            f"{counted(disp['critical']['cells'], 'cell')} to {critical_words(disp)} ({there}); each cell is a link to "
            "it in the "
            f'drawing:</p><ol class="chain">{"".join(items)}</ol>')


def critical_path_html(s):
    if s.sch is None:
        return f'<p class="empty">The critical path is {esc(s.sch_note or "not computed yet")}.</p>'
    sc = s.sch["scored"]
    path = sc["path"]
    disp = s.sch.get("display") or {}
    same = disp.get("params") == sc["params"]
    linked = same and disp.get("drawn") and s.svg is not None
    inputs = {pt["name"] for pt in s.t.task.get("ports", {}).get("inputs", [])}

    def from_input(n):
        """A path's first net is an input port's bit, or on a clocked netlist a flip-flop's Q."""
        return not sc.get("sequential") or re.sub(r"\[\d+\]$", "", n["net"]).lstrip("\\") in inputs
    rows, prev = [], None
    for k, n in enumerate(path):
        stage = "" if prev is None else esc(f"{n['arrival_ps'] - prev:.1f}")
        prev = n["arrival_ps"]
        driver = ((sch_link(s, n["inst"], code(n["inst"])) if linked else code(n["inst"])) if n["inst"] else
                  '<span class="muted">input port</span>' if k == 0 and from_input(n) else
                  '<span class="muted">flop Q</span>')
        rows.append([str(k), code(n["net"]), esc({"r": "rise", "f": "fall"}[n["edge"]]), driver,
                     code(n["cell"]) if n["cell"] else '<span class="muted">–</span>',
                     esc(f"{n['arrival_ps']:,.1f}".replace(",", " ")), esc(f"{n['slew_ps']:.1f}"), stage])
    table = page.table(heads("#", "net", "edge", "driven by", "cell", "arrival (ps)", "transition (ps)", "stage (ps)"),
                       rows, numeric=(0, 5, 6, 7), cls="path")
    first = path[0] if path else None
    at = f"at the scoring point {esc(point_words(sc['params'], s.t))}" if sc["params"] else "at the task's one size"
    names = ("the instance names are the schematic's (the same netlist), each a link to its cell there" if linked else
             "the instance names are the schematic's (the same netlist)" if same else
             "the instance names are the scored netlist's, not the schematic's (drawn at a smaller size)")
    if sc.get("sequential"):
        lead = (f"<p>The path the ranked register-to-register period ends on, {at}: "
                f"{counted(len(path), 'net')}, {counted(sc['critical']['cells'], 'cell')}, to {critical_words(sc)}; "
                f"the period, {thin(sc['delay_ps_sky130'])} ps, is the last arrival plus that flip-flop's setup time "
                "(ideal clock). ")
    else:
        lead = (f"<p>The path the ranked delay ends on, {at}: "
                f"{counted(len(path), 'net')}, {counted(sc['critical']['cells'], 'cell')}, to {critical_words(sc)} at "
                f"{thin(sc['delay_ps_sky130'])} ps. ")
    lead += ("Each row is a net of the repaired netlist with the arrival and the "
            "transition the STA computed there (NLDM tables, the larger transition carried; no wires). "
            + (f"The first row is an input: its arrival is the input driver's own delay ({drive_words(sc)} fed by a "
               f"{sc.get('setup', {}).get('pi_slew_ps', 50)} ps ramp). " if first and not first["inst"]
               and from_input(first) else
               "The first row is a flip-flop's Q: its arrival is the flop's clock-to-Q delay after the clock edge. "
               if first and not first["inst"] else "")
            + f"From {code('ppa.py --path')} ({code('critical_path_timing')}); {names}.</p>")
    chain = drawn_path_html(s) if not same and disp.get("drawn") and s.svg is not None else ""
    if len(rows) > 40:
        return lead + chain + page.details(f"every stage ({len(rows)} rows)", table)
    return lead + chain + table


def load_ge_tables():
    """The pinned GE table of each scoring flow (leaderboard.py `FLOW_FILES`): score/ge.json for the combinational
    flow, score/ge_seq.json (the same weights plus the flip-flop) for the clocked one."""
    return {flow: json.loads(read_text(f"svgolf/score/{files[1]}")) for flow, files in lb.FLOW_FILES.items()}


def subject_flow(s):
    """The scoring flow of a detail page's numbers: a record's own (`checker.flow`), else its task's kind's."""
    return lb.record_flow(s.rec) if s.rec else lb.task_flow(s.t.task)


def cells_html(s, ge_tables):
    t = s.t
    p = s.ppa
    rec_score = s.rec["score"] if s.rec else (s.ref or {}).get("score")
    flow = subject_flow(s)
    ge_part = (page.details(f"the gate mix of the extra GE column (the pinned GE table, "
                            f"{code('score/' + lb.FLOW_FILES[flow][1])})", gates_html(rec_score, ge_tables[flow]))
               if rec_score and rec_score.get("gates") else "")
    if not p or not p.get("cell_hist_sky130"):
        return (f'<p class="empty">No sky130 cell list: {esc(s.sch_note or "this design has no sky130 weighing")}.</p>'
                + ge_part)
    hist = p["cell_hist_sky130"]
    areas = (s.sch or {}).get("cell_area_e4um2") or {}
    rows = sorted(hist.items(), key=lambda kv: (-kv[1] * areas.get(kv[0], 0), -kv[1], kv[0]))
    total = p.get("area_e4um2_sky130")
    bars = ([(c, round(areas[c] * n / 10000, 2), f"µm² · {counted(n, 'cell')}") for c, n in rows] if all(c in areas for c in hist)
            else [(c, n, "cells") for c, n in rows])
    svg = svgplot.bar_chart(bars, title="the cells of the repaired netlist, by area",
                            unit="µm²" if all(c in areas for c in hist) else "cells") if len(bars) > 1 else ""
    trows = [[code(c), esc(thin(n)), esc(lb.fmt_um2(areas[c])) if c in areas else "–",
              esc(lb.fmt_um2(areas[c] * n)) if c in areas else "–",
              esc(f"{areas[c] * n * 100 / total:.1f}%") if c in areas and total else "–"] for c, n in rows]
    trows.append(["<strong>total</strong>", f"<strong>{esc(thin(sum(hist.values())))}</strong>", "",
                  f"<strong>{esc(lb.fmt_um2(total))}</strong>", ""])
    checks = ""
    if areas and total is not None and sum(areas[c] * n for c, n in hist.items() if c in areas) != total:
        checks = '<p class="fine">(The cells do not add up to the area: a stale cell list.)</p>'
    rp, leg = p.get("repair") or {}, p.get("legality") or {}
    facts = []
    if rp:
        facts.append(f"Repair ({code(rp.get('method', ''))}): {counted(rp.get('buffers', 0), 'buffer')} on "
                     f"{counted(rp.get('nets_buffered', 0), 'net')}, {counted(rp.get('tie_cells', 0), 'tie cell')}, "
                     f"{counted(rp.get('rounds', 1), 'weighing round')}; nothing is resized.")
    if leg:
        facts.append(f"Legality: worst load {leg.get('worst_load_ratio')} × {code('max_capacitance')}, worst transition "
                     f"{leg.get('worst_transition_ratio')} × {code('max_transition')}; {leg.get('table_reads_outside', 0)} "
                     "timing-table reads outside the characterized grid.")
    figure = (f'<figure class="chart-figure">{svg}<figcaption>The area of each cell type in the repaired A0′ netlist, at '
              "the scoring point: the count times the cell's area in the pinned liberty. Their sum is the ranked area."
              "</figcaption></figure>"
              if svg else "")
    return (figure + page.table(heads("cell", "count", "µm² each", "µm² in all", "share"), trows, numeric=(1, 2, 3, 4))
            + checks + "".join(f'<p class="fine">{f}</p>' for f in facts) + ge_part)


# A licence notice a design may carry in full instead of an SPDX identifier: its SPDX identifier -> sentences that
# must all appear in the source's comments (comment markers and line breaks ignored). The MIT notice is its grant
# and its condition (MIT-0 has the grant alone): the sorter's reference, adapted from andrewpeck/cell-sort.
LICENCE_NOTICES = {
    "MIT": ("Permission is hereby granted, free of charge, to any person obtaining a copy of this software and "
            "associated documentation files",
            "The above copyright notice and this permission notice shall be included in all copies or substantial "
            "portions of the Software."),
}


def licence_ids(sv_text):
    """The licences a design's source declares: its SPDX identifiers, and the identifier of every notice of
    LICENCE_NOTICES it carries in full."""
    ids = set(re.findall(r"SPDX-License-Identifier:\s*([^\n]+?)\s*$", sv_text, re.M))
    prose = " ".join(" ".join(re.sub(r"^\s*(//+|/\*+|\*+/?)", "", ln) for ln in sv_text.split("\n")).split())
    ids |= {i for i, sentences in LICENCE_NOTICES.items() if all(x in prose for x in sentences)}
    return sorted(ids)


def licence_html(s, sv_text):
    """For a design adapted from licensed code (an SPDX identifier in its source, or a licence notice it carries in
    full, `licence_ids`): the identifiers, that the notices are kept in the file shown, and the licence texts that
    ship beside it (copied to the site)."""
    ids = licence_ids(sv_text)
    if not ids:
        return ""
    texts = []
    if s.ref is not None:
        lic = posixpath.join(posixpath.dirname(s.ref["sv"]), "LICENSES")
        if os.path.isdir(repo_file(lic)):
            texts = sorted(f for f in os.listdir(repo_file(lic)) if f.endswith(".txt"))
            texts = [page.link(rel_link(s.here, f"tasks/{s.t.name}/reference/LICENSES/{f}"), code(f)) for f in texts]
    # a reference's file names its changes to upstream (its header); a player's design need not, so its card says
    # only what licence_ids found: the notice, in the file
    kept = ("the copyright, provenance and licence notices and the list of changes are kept in the design file"
            if s.ref is not None else "its licence notice is in the design file")
    return (f'<p class="licence">Adapted from licensed code ({", ".join(code(i) for i in ids)}): {kept}, shown in '
            "full below" + (f"; the licence texts: {and_list(texts)}" if texts else "") + ".</p>")


def reproduce_html(s):
    t = s.t
    src = (f"tasks/{t.name}/{posixpath.relpath(s.ref['sv'], t.dir)}" if s.ref is not None
           else f"{s.rec['record_hash']}.sv")
    # a clocked task is weighed through the clocked flow (`--seq`, as its record was): without it the comb flow
    # refuses the netlist's flops
    seq = metrics.is_clocked(t.task)
    cmd = (f"# the ranked numbers, at the scoring point (from svgolf/, with the pinned Yosys and liberty)\n"
           + ("# a clocked task: the clocked flow, --seq (the time is the register-to-register period)\n"
              if seq else "")
           + f"python3.12 score/ppa.py {src} --task tasks/{t.name}{' --seq' if seq else ''} --path \\\n"
           "    --json out.json --netlist scored.v --repaired-netlist repaired.v\n")
    expect = []
    p = s.ppa or {}
    sc = s.rec["score"] if s.rec else None
    if sc and sc.get("rtlil_sha256"):
        expect.append(("score.rtlil_sha256", code(sc["rtlil_sha256"])))
    if p.get("netlist_sha256"):
        expect.append(("ppa.netlist_sha256", code(p["netlist_sha256"])))
    if (p.get("repair") or {}).get("netlist_sha256"):
        expect.append(("ppa.repair.netlist_sha256", code(p["repair"]["netlist_sha256"])))
    if p.get("area_e4um2_sky130") is not None:
        expect.append(("ppa.area_e4um2_sky130", code(str(p["area_e4um2_sky130"]))))
        expect.append(("ppa.delay_ps_sky130", code(str(p["delay_ps_sky130"]))))
    parts = ["<p>From " + code("svgolf/") + ", with the pinned tools (" + page.link(rel_link(s.here, REPRODUCE_PAGE),
             "reproduce a score") + " lists them):</p>",
             page.code_block(cmd, "bash", name="shell", term=True)]
    if expect:
        parts.append("<p>Expect, in " + code("out.json") + ":</p>" + page.dl(expect))
    if s.sch is not None and s.sch["display"].get("drawn"):
        disp = s.sch["display"]
        prm = " ".join(f"--param {k}={v}" for k, v in disp["params"].items())
        parts.append("<p>The schematic and the critical-path data are " + code(f"site/schematics/{t.name}/{s.sv_sha[:16]}.json")
                     + " and its " + code(".svg") + ", written by " + code("site/gen_schematics.py") + " (the display "
                     "instance is " + code(f"ppa.py ... {prm} --repaired-netlist") + ", drawn by netlistsvg "
                     f"{esc(s.sch['tools']['netlistsvg'])}; repaired netlist sha256 "
                     + code(disp["repaired_sha256"][:16] + "…") + ").</p>")
    return "".join(parts)


def reproduce_asap7_html(s7):
    """The ASAP7 view's "Reproduce": the same command with `--pdk asap7` (the five pinned ASAP7 liberty files) and the
    numbers to expect, those of the design's entry in leaderboard/asap7/<task>.json; or why there are none."""
    t = s7.t
    e = (s7.ppa or {}).get("entry")
    if e is None:
        return f'<p class="empty">No ASAP7 numbers for this design yet (leaderboard/asap7/{esc(t.name)}.json).</p>'
    src = (f"tasks/{t.name}/{posixpath.relpath(s7.ref['sv'], t.dir)}" if s7.ref is not None
           else f"{s7.rec['record_hash']}.sv")
    seq = metrics.is_clocked(t.task)
    cmd = ("# the ASAP7 view's numbers, at the scoring point (from svgolf/, with the pinned Yosys; once:\n"
           "# python3.12 score/ppa.py --pdk asap7 --fetch-liberty, the five pinned ASAP7 files into score/lib/asap7/)\n"
           f"python3.12 score/ppa.py {src} --task tasks/{t.name}{' --seq' if seq else ''} --pdk asap7 --no-mapped "
           "\\\n    --json out.json\n")
    expect = [("ppa.netlist_sha256", code(e["netlist_sha256"])), ("ppa.repair.netlist_sha256", code(e["repaired_sha256"])),
              ("ppa.area_e5um2_asap7", code(str(e["area_e5um2"]))), ("ppa.delay_ps_asap7", code(str(e["delay_ps"])))]
    return ("<p>From " + code("svgolf/") + ", with the pinned tools (" + page.link(rel_link(s7.here, REPRODUCE_PAGE),
            "reproduce a score") + " lists them):</p>" + page.code_block(cmd, "bash", name="shell", term=True)
            + "<p>Expect, in " + code("out.json") + ":</p>" + page.dl(expect)
            + f"<p>{code(f'leaderboard/asap7/{t.name}.json')} keeps these numbers; "
            + code(f"python3.12 leaderboard/leaderboard.py asap7 --rescore --task {t.name}")
            + " weighs every design of the task again and compares, bit for bit.</p>")


def detail_head(s, title_html, status, lead, kind):
    t, here = s.t, s.here
    tags = [status] if status else []
    tags.append(page.badge(f"scored at {point_text(t.point)}", "plain"))
    return page.page_head(
        crumbs_html=(f'<a href="{rel_link(here, "index.html")}"><span class="back" aria-hidden="true">‹</span>'
                     f'Tasks</a> / <a href="{rel_link(here, t.page)}">{esc(t.name)}</a> / {esc(kind)}'),
        title_html=title_html, tags_html=" ".join(tags), lead_html=lead)


def overview_parts(site, s):
    """(the overview's inner HTML: the dashboard, or why there are no ranked numbers; the area-time plot's inner HTML,
    or None) of the subject `s` in the view of its task (`s.t.pdk`)."""
    t = s.t
    pdk = t.pdk
    p = par_design(t)
    par = st_point(p, pdk) if p is not None and p["exact"] is not None else None
    designs = plotted(t)
    if s.d is None:
        why = (lb.unranked_reason(s.rec, t.task, flow=t.flow, identity=site.ppa_identity, input_drive=t.drive,
                                  statement=t.statement, pdk=pdk, asap7=t.a7_table, asap7_identity=site.a7_identity)
               if s.rec else None) or f"no {PDK_NAME[pdk]} weighing at the scoring point"
        return f'<p class="empty">No ranked numbers to show: {esc(why)}.</p>', None
    recs = [{"id": r["record_hash"], "kind": "record", "player": r["player"], "area": lb.row_area(r),
             "time": r["time_ps"]} for r in t.ranked()]
    st = standing.standing(st_point(s.d, pdk), recs, par, [st_point(d, pdk) for d in designs])
    return dashboard_html(s, st, par, designs), area_time_html(s, par)


def asap7_block(site, s):
    """The ASAP7 view's weighing of the subject's design, shaped as the dashboard reads a record's `ppa` block (its
    cells, repair, flops, unit depth and input drive), from its entry in leaderboard/asap7/<task>.json (`entry`
    too), or None."""
    t = s.t
    e = lb.asap7_entry(t.a7_table, s.sv_sha)
    if e is None or (s.rec is not None and lb.asap7_binding_problems(e, s.rec)):
        return None
    return {"cells_asap7": e["cells"], "repair": {"buffers": e["buffers"], "tie_cells": e["tie_cells"],
                                                  "netlist_sha256": e["repaired_sha256"]},
            "flops": e["flops"], "unit_depth": e["depth"], "netlist_sha256": e["netlist_sha256"],
            "setup": {"input_drive": (site.a7_identity or {}).get("input_drive")}, "entry": e}


def detail_sections(site, s, ge_tables):
    """The parts every detail page shares: (the overview, the area-time plot, the netlist card, the subject in the
    ASAP7 view). The overview is the dashboard (or why there are no ranked numbers, with no plot then), in both
    views (`dual`: the library selector); the netlist card holds the schematic, the critical path and the cells as
    three tabs (page.tabs: without the script, three panes one under the other), from the sky130 weighing."""
    t = s.t
    load_schematic(site, s)
    sky_over, sky_plot = overview_parts(site, s)
    with t.view("asap7"):
        s7 = Subject(t, s.here, rec=s.rec, ref=s.ref)
        s7.ppa = asap7_block(site, s7)
        if s7.ppa is None:
            s7.d = None
        a7_over, a7_plot = overview_parts(site, s7)
    a7_over = suffix_ids(a7_over, "-asap7")
    a7_plot = suffix_ids(a7_plot, "-asap7") if a7_plot else None
    if s.d is not None:
        overview = f'<section id="dashboard" aria-label="the ranked numbers">{dual(sky_over, a7_over)}</section>'
    else:
        overview = page.card(dual(sky_over, a7_over), tag="section", id_="dashboard", title_html="Area, time and score")
    plot = ""
    if sky_plot or a7_plot:
        def none(lib):
            return f'<p class="empty">No {lib} numbers for this design: nothing to plot.</p>'
        plot = page.card(dual(sky_plot, a7_plot or none("ASAP7")) if sky_plot else a7_plot, tag="section",
                         id_="area-time", title_html="Area against time",
                         actions_html=f'<span class="label">{nocase(esc("µm² × ps · lower left is better"))}'
                                      f'{pdk_text("", " · ASAP7")}</span>')
        if not sky_plot:                 # numbers in the ASAP7 view only: the card is that view's alone
            plot = f'<div class="pdk-asap7">{plot}</div>'
    # each pane says the size it shows (the drawing is at a smaller one, the other two at the scoring point), as the
    # three cards' heads did
    disp = (s.sch or {}).get("display") or {}
    drawn = (scale_label(f"drawn at {point_words(disp['params'], t)}")
             if disp.get("drawn") and disp["params"] != s.sch["scored"]["params"] else "")
    scored = scale_label(f"at {point_text(t.point)} · scored")
    a7_note = ('<p class="pdk-asap7 pdk-note small">The netlist card shows the sky130 weighing (its cells, its '
               "critical path): the ASAP7 view changes the overview above, not this card.</p>")
    netlist = page.card(a7_note + page.tabs([("schematic", "Schematic", drawn + schematic_html(s)),
                                             ("critical-path", "Critical path", scored + critical_path_html(s)),
                                             ("cells", "Cells", scored + cells_html(s, ge_tables))],
                                            label_text="the netlist: schematic, critical path, cells"),
                        tag="section", id_="netlist", title_html="The netlist")
    return overview, plot, netlist, s7


def scale_label(text):
    """The size a netlist pane shows ("drawn at N = 4", "at N = 16 · scored"), at its top right."""
    return f'<p class="label pane-scale">{esc(text)}</p>'


def detail_layout(overview, sources, main, side, after, more=()):
    """A detail page's body under its head: the overview, then the sources, across the page (the code at the page's
    width: in a column its lines ran past the edge), then two columns (the main one: the netlist, and under it `more`,
    a record's checker detail, beside the rest of the side one; the side one: the record's or the reference's facts
    and the proof's), then what needs the page's width (a clocked record's post-synthesis table, the area-time plot,
    a diff, reproduce). In one column (under 72rem) the order is the netlist, the side column's cards, then `more`:
    a record's player, date and notes come before its checker detail."""
    extra = f'<div class="col col-main col-more" id="more-col">{"".join(more)}</div>' if more else ""
    return (overview + sources + f'<div class="split split-detail{" split-more" if more else ""}">'
            f'<div class="col col-main" id="main-col">{"".join(main)}</div>'
            f'<div class="col col-side" id="side-col">{"".join(side)}</div>{extra}</div>' + "".join(after))


def sources_card(s, sv_text, lean_text, sv_name, lean_name, sv_src, lean_src, lines, downloads):
    """The sources: the design file in a code box (its head names it and downloads it under that name), the proof
    folded under it, a licence's notice above them."""
    dl_ = " ".join(f'<a class="codebox-dl" href="{esc(rel_link(s.here, href))}" download="{esc(sv_name)}">'
                   f"{esc(text)}</a>" for href, text in downloads)
    return page.card(licence_html(s, sv_text)
                     + page.code_block(sv_text, "sv", src=sv_src, name=sv_name, actions_html=dl_)
                     + page.details(f"{code(lean_name)} ({lines} code lines)", page.code_block(lean_text, "lean",
                                                                                                src=lean_src)),
                     tag="section", id_="sources", title_html="The sources")


def status_badge_of(t, rec):
    """A player's record's place on the board, as a badge (or None)."""
    row = next((r for r in t.ranked() + t.board["unranked"] if r["record_hash"] == rec["record_hash"]), None)
    if row in t.board["frontier"]:
        return page.badge("on the Pareto frontier", "frontier")
    if row in t.board["unranked"]:
        return page.badge("not ranked", "draft")
    if row:
        return page.badge(f"layer {row['layer']}", "layer")
    return None


def record_page(site, t, rec, ge_tables):
    h = rec["record_hash"]
    here = f"tasks/{t.name}/records/{h}.html"
    base = f"tasks/{t.name}/records/{h}"
    data_rel = f"svgolf/leaderboard/data/{t.name}/{h}"
    for ext in (".json", ".sv", ".lean"):
        site.copy(base + ext, data_rel + ext)
    sc, proof, chk, ps = rec["score"], rec["proof"], rec["checker"], rec["postsynth"]
    is_ref = rec["player"] == site.config["reference_player"]
    ref = t.ref_of_record.get(h)
    s = Subject(t, here, rec=rec, ref=ref if is_ref else None)
    lead = None
    if is_ref:
        what = (f"the proved reference {code(ref['stem'])}: its design and its proof "
                f"{code(posixpath.basename(ref['lean']))} ({ref['proof_lines']} code lines)"
                + (f". {md_inline(ref['description'])}" if ref["description"] else ".")) if ref else \
            "a design of the maintainers that is not one of the task's proved references."
        # par in a view only where that view's par is this reference (the two libraries may choose different ones),
        # as on a reference's own page
        lead = (f"<p>Recorded by the maintainers from {what} The record shows that reference passing the "
                "whole checker. It is "
                + both(t, lambda: "par, the bar to beat" if ref is not None and t.par is ref else "shown with par",
                       inline=True)
                + ", not a player's entry, and it is not ranked among "
                f"the submissions ({page.link(rel_link(here, t.page + '#references'), 'proved references')}).</p>")
    status = (both(t, lambda: page.badge("reference: par, not an entry" if ref is not None and t.par is ref
                                         else "reference: not an entry", "par"), inline=True) if is_ref
              else both(t, lambda: status_badge_of(t, rec) or "", inline=True))
    head = detail_head(s, f"Record {code(h[:12])}", status, lead, "record")
    overview, plot, netlist, s7 = detail_sections(site, s, ge_tables)

    def card(i, title_html, content_html):
        return page.card(content_html, tag="section", id_=i, title_html=title_html)
    files = rec["files"]
    prev = None if is_ref else previous_frontier_record(rec, t.player_records)
    same_day = [] if is_ref else same_day_records(rec, t.player_records)
    same_day_note = ("" if not same_day else
                     f"{counted(len(same_day), 'other submission')} {'is' if len(same_day) == 1 else 'are'} dated the "
                     f"same day ({esc(rec['submitted_at'][:10])}), which does not order "
                     f"{'it' if len(same_day) == 1 else 'them'}")
    sv_text = read_text(data_rel + ".sv")
    lean_text = read_text(data_rel + ".lean")
    # par is not compared with the submissions before it; a submission with none dated before it has nothing to
    # compare with, which the record's facts say (a diff needs the page's width, so it has its own card under the
    # columns): the task's first, or one whose earlier-or-equal records share its day (`submitted_before`)
    none_before = (f"none: no submission of this task is dated before this one; {same_day_note}" if same_day else
                   "none: this is the task's first submission")
    first = [] if is_ref or prev else [("previous frontier", f'<span id="diff">{none_before}</span>')]
    record = card("record", "The record", page.dl([
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
    ] + first))
    proof_card = card("proof", "The proof", page.dl([
        ("code lines", str(proof.get("lines"))),
        ("build time", esc(f"{proof.get('build_seconds')} s")),
        ("axioms", ", ".join(code(a) for a in proof.get("axioms", []))),
        ("tactics seen", ", ".join(code(x) for x in proof.get("tactics", [])) or "none"),
        ("imports", ", ".join(code(x) for x in proof.get("imports", []))),
    ]))
    flow_rows = [("Yosys", chk.get("yosys")), ("Verilator", chk.get("verilator")), ("Lean toolchain", chk.get("lean_toolchain")),
                 ("svGolf revision", chk.get("svgolf_revision")), ("lean-surfaces revision", chk.get("lean_surfaces_revision")),
                 ("canonicalization script", chk.get("canon_script_sha256")), ("scoring script", chk.get("script_sha256")),
                 ("GE table", chk.get("ge_table_sha256")), ("extractor", chk.get("extractor_sha256")),
                 ("canonical RTLIL", sc.get("rtlil_sha256"))]
    mism = lb.flow_mismatch(lb.flow_of(rec), t.flow)
    flow_note = ("<p>Checked under the pinned flow of this site's boards.</p>" if not mism else
                 f"<p>Checked under another flow ({esc(', '.join(mism))} differ): not ranked.</p>")
    checker = card("checker", "Checker and flow", flow_note
                   + page.dl([(k, code(v) if v else '<span class="muted">not recorded</span>') for k, v in flow_rows])
                   + page.details("the checker's files (sha256)", page.table(
                       ["file", "sha256"], [[f'<code>{esc(f).replace("/", "/<wbr>")}</code>', code(s_)]
                                            for f, s_ in sorted(chk.get("files", {}).items())], cls="hashes")))
    if isinstance(ps.get("points"), list):         # a clocked record's (its table goes across the page)
        postsynth = card("postsynth", "Post-synthesis check", postsynth_clocked_html(t, ps))
    else:
        ps_rows = [("mode", esc(lb.record_mode(ps))), ("vectors", esc(ps.get("vectors"))),
                   ("mismatches", esc(ps.get("mismatches"))), ("point", esc(ps.get("point", ""))),
                   ("seed", code(ps.get("seed", ""))),
                   ("salted", "yes (a secret salt: the vectors were not predictable)" if ps.get("salted") else "no")]
        if "full_vectors" in ps:
            ps_rows.insert(2, ("full set", esc(ps["full_vectors"])))
        agreed = ("agreed on every one" if ps.get("mismatches") == 0
                  else f"disagreed on {ps.get('mismatches')} (a record the checker accepted should have none)")
        postsynth = card("postsynth", "Post-synthesis check",
                         f"<p>ls-sv's reading of the design and the scored netlist, simulated on the same vectors, "
                         f"{esc(agreed)}. The vectors are a sample of the inputs: a guard against the two tools "
                         "disagreeing, not a proof.</p>" + page.dl(ps_rows))
    diff = ""
    if prev:
        p = f"svgolf/leaderboard/data/{t.name}/{prev['record_hash']}"
        diff = card("diff", "Against the previous frontier record", f"<p>Compared with "
                    f"{record_link(t, here, prev['record_hash'])} by {esc(prev['player'])}, the best record "
                    "before this one." + (f" {same_day_note[:1].upper()}{same_day_note[1:]}." if same_day else "")
                    + "</p>"
                    + diff_html(read_text(p + ".sv"), sv_text, f"{prev['record_hash'][:12]}.sv", f"{h[:12]}.sv")
                    + page.details("the proofs' diff", diff_html(read_text(p + ".lean"), lean_text,
                                                                 f"{prev['record_hash'][:12]}.lean", f"{h[:12]}.lean")))
    sources = sources_card(s, sv_text, lean_text, files["sv"]["name"], files["lean"]["name"], data_rel + ".sv",
                           data_rel + ".lean", proof.get("lines"), [(base + ".sv", "download")])
    verify = (f"# re-run the whole check on this record's files (the cost of the original check)\n"
              f"H={h}\n"
              f"mkdir -p rec/{t.name} && cp \"$H.json\" \"$H.sv\" \"$H.lean\" rec/{t.name}/\n"
              f"python3.12 leaderboard/leaderboard.py verify --data-dir rec --task {t.name} --full\n")
    reproduce = card("reproduce", "Reproduce and verify", dual(reproduce_html(s), reproduce_asap7_html(s7))
                     + "<h3>Verify the record</h3><p>Download the three files, then from <code>svgolf/</code>:</p>"
                     + page.code_block(verify, "bash", name="shell", term=True)
                     + "<p><code>verify --offline</code> checks only the hashes and the arithmetic; plain "
                       "<code>verify</code> also rescores the design (no Lean; seconds for most designs, a minute or "
                       "more for the largest), on sky130 and on ASAP7.</p>")
    # the checker's card and a combinational record's post-synthesis facts fit the main column, under the netlist;
    # a clocked record's per-point table needs the page's width (with the column, its point column wrapped and its
    # table scrolled), so it comes first under the columns
    clocked_ps = isinstance(ps.get("points"), list)
    body = head + detail_layout(overview, sources, [netlist], [record, proof_card],
                                ([postsynth] if clocked_ps else []) + [plot, diff, reproduce],
                                more=[checker] + ([] if clocked_ps else [postsynth]))
    site.page(here, f"{t.name} record {h[:12]}", body, scripts=("charts.js",), scores=True,
              description=f"svGolf {t.name}: record {h[:12]} by {rec['player']}")


def postsynth_clocked_html(t, ps):
    """The post-synthesis card of a CLOCKED record (leaderboard/README.md, `postsynth`: `points`, each with its
    `seeds`): what ran, at which points, from which power-ups, how long, and the mismatches; every seed's draw in a
    table below. The words for the check are the reactive kind's (check/postsynth.py, THE REACTIVE CHECK) on a
    react-family task, a neutral sentence on the other clocked kinds."""
    points = ps["points"]
    seeds = [sd for pt in points for sd in pt.get("seeds") or []]
    per_point = sorted({len(pt.get("seeds") or []) for pt in points})
    n_seeds = per_point[0] if len(per_point) == 1 else None
    unit = ("segments" if any("segments" in sd for sd in seeds) else
            "transactions" if any("transactions" in sd for sd in seeds) else None)
    per_seed = sorted({sd[unit] for sd in seeds}) if unit else []
    stim = (f"{thin(per_seed[0])} {unit}" if len(per_seed) == 1 else f"{unit}") if unit else "its cycles"
    mism = ps.get("mismatches")
    agreed = ("no mismatch" if mism == 0
              else f"{mism} mismatches (a record the checker accepted should have none)")
    seeds_words = f"{n_seeds} seeds per point" if n_seeds else "its seeds"
    runs = f"{n_seeds} times, once per seed" if n_seeds else "once per seed"
    if t.kind == "react-family":
        rst = ((t.task.get("reset") or {}).get("port") if isinstance(t.task.get("reset"), dict) else None) or "rst"
        what = (f"<p>At each point below, the check ran the scored netlist and ls-sv's reading of the design "
                f"{esc(runs)}, each run from a power-up state and through a seeded stimulus of {esc(stim)}: a reset "
                f"entry, then entries with {code(rst)} = 0, the last segment a long run without a reset. On every "
                "cycle of every run the netlist's outputs met the task's guarantee, and the outputs sampled just "
                "before each rising edge equalled the snapshot before (the Moore sample). Where the two runs start "
                "from the same state (seed 0, the all-zeros power-up, unless the pinned flow turned a register into a "
                "constant 1) the netlist's outputs equalled ls-sv's bit for bit; from two different power-ups a "
                "correct design may answer differently, and ls-sv's outputs met the guarantee too. The check found "
                f"{esc(agreed)}. The stimulus is a sample of the input traces: a guard against the two tools "
                "disagreeing, not a proof.</p>")
    else:
        # a latency kind checks each point against its own latency, the solution's `lat` there (F8; the record's
        # `latency` per point, from check.py's `latency_at`)
        timed = (" Each point ran against its own latency, the solution's " + code("lat") + " at that point (the "
                 "table's latency column): every transaction had to finish within it."
                 if any(pt.get("latency") is not None for pt in points) else "")
        what = (f"<p>At each point below, the check ran the scored netlist and ls-sv's reading of the design "
                f"{esc(runs)}, each run from a power-up state and through a seeded stimulus of {esc(stim)}.{timed} "
                f"The check found {esc(agreed)}. The stimulus is a sample of the inputs: a guard against the two tools "
                "disagreeing, not a proof.</p>")
    scored = {k: v for k, v in (t.point or {}).items()}
    pt_names = [esc(point_text(pt.get("params") or {})) + (" (the scoring point)" if pt.get("params") == scored else "")
                for pt in points]
    salted = any(sd.get("salted") for sd in seeds)
    starts = sorted({sd.get("lssv_start", "") for sd in seeds if sd.get("seed") == 0})
    rows = [("mode", esc(lb.record_mode(ps))),
            ("points", ", ".join(pt_names)),
            ("seeds", esc(seeds_words) + (": seed 0 from the all-zeros power-up, every other one from a random "
                                          "power-up drawn from its seed (below)" if starts == ["zeros"] else "")),
            ("stimulus", esc(f"{stim} per seed")),
            ("clock cycles", esc(f"{thin(sum(sd.get('cycles', 0) for sd in seeds))} in all")),
            ("mismatches", esc(mism)),
            ("salted", "yes (a secret salt: the stimulus was not predictable)" if salted else
             "no (the default empty salt: anyone can run this exact stimulus again)"),
            ("scored netlist", f"sha256 {code(ps.get('netlist_sha256', ''))}")]
    # the latency each point was checked at (cycles): a latency kind's record only (the reactive kind has none)
    lat_col = any(pt.get("latency") is not None for pt in points)
    headers = (["point"] + (["latency (cycles)"] if lat_col else []) + ["seeds", "clock cycles"]
               + ([unit] if unit else []) + ["mismatches", "netlist sha256"])
    trows = [[esc(point_text(pt.get("params") or {}))]
             + ([esc(pt["latency"]) if pt.get("latency") is not None else '<span class="muted">–</span>']
                if lat_col else [])
             + [esc(len(pt.get("seeds") or [])), esc(thin(sum(sd.get("cycles", 0) for sd in pt.get("seeds") or [])))]
             + ([esc(thin(sum(sd.get(unit, 0) for sd in pt.get("seeds") or [])))] if unit else [])
             + [esc(pt.get("mismatches")), code((pt.get("netlist_sha256") or "")[:12])] for pt in points]
    srows = [[esc(point_text(pt.get("params") or {})), esc(sd.get("seed")),
              code(sd.get("lssv_start", "")) if sd.get("lssv_start") else '<span class="muted">–</span>',
              code(sd.get("netlist_randseed", "")) if "netlist_randseed" in sd else '<span class="muted">–</span>',
              esc(thin(sd.get("cycles", 0)))] + ([esc(thin(sd.get(unit, 0)))] if unit else [])
             + [code((sd.get("seed_sha256") or "")[:12])]
             for pt in points for sd in pt.get("seeds") or []]
    seed_table = page.table(["point", "seed", "ls-sv power-up", "netlist randSeed", "clock cycles"]
                            + ([unit] if unit else []) + ["draw"], srows, numeric=(1, 4, 5) if unit else (1, 4))
    return (what + page.dl(rows) + page.table(headers, trows, numeric=tuple(range(1, len(headers) - 1)))
            + page.details(f"every seed's run ({len(srows)})", "<p>A seed's draw is "
                           f"{code('sha256(salt, task, point, seed)')} (its first 12 digits below; check/postsynth.py "
                           f"{code('seed_draw')}). Everything random in the seed's run comes from it: the stimulus, "
                           f"ls-sv's power-up ({code('zeros')} for seed 0, else {code('seed:<k>')}) and the netlist's "
                           f"Verilator {code('randSeed')}, which the all-zeros power-up of seed 0 does not use.</p>"
                           + seed_table))


def licence_texts(site, t):
    """The licence texts that ship beside a task's licensed references (reference/LICENSES/*.txt), offered byte for
    byte next to the references' downloads (a design page links them from its notices)."""
    dirs = sorted({posixpath.join(posixpath.dirname(r["sv"]), "LICENSES") for r in t.refs
                   if "SPDX-License-Identifier" in read_text(r["sv"])})
    for lic in dirs:
        if os.path.isdir(repo_file(lic)):
            for f in sorted(os.listdir(repo_file(lic))):
                if f.endswith(".txt"):
                    site.copy(f"tasks/{t.name}/reference/LICENSES/{f}", f"{lic}/{f}")


def reference_detail_page(site, t, ref, ge_tables):
    """The detail page of a proved reference that has no record (tasks/<t>/reference/<stem>.html, beside its
    downloads): the same sections as a record page, from the reference's files, its scores and its site/schematics
    data."""
    here = reference_page(t, ref)
    s = Subject(t, here, ref=ref)
    status = both(t, lambda: page.badge("par: the bar to beat" if t.par is ref else "proved reference", "par"),
                  inline=True)
    desc = f" {md_inline(ref['description'])}" if ref["description"] else ""
    lead = (f"<p>A proved reference of {code(t.name)}, written or adapted by the maintainers and shipped with the "
            "task: its "
            f"design and its proof {code(posixpath.basename(ref['lean']))} ({ref['proof_lines']} code lines).{desc} "
            "It is " + both(t, lambda: 'par, the bar to beat' if t.par is ref else 'shown with par', inline=True)
            + ", never a player's entry "
            f"({page.link(rel_link(here, t.page + '#references'), 'proved references')}).</p>")
    head = detail_head(s, f"Reference {code(ref['stem'])}", status, lead, "reference")
    overview, plot, netlist, s7 = detail_sections(site, s, ge_tables)
    sv_text, lean_text = read_text(ref["sv"]), read_text(ref["lean"])
    base = f"tasks/{t.name}/reference/{ref['stem']}"
    facts = page.card(page.dl([
        ("task", page.link(rel_link(here, t.page), code(t.name))),
        ("design", f"{code(posixpath.basename(ref['sv']))} sha256 {code(ref['sha256'])}"),
        ("proof", f"{code(posixpath.basename(ref['lean']))}, {ref['proof_lines']} code lines"),
        ("tactics seen", ", ".join(code(x) for x in ref["tactics"]) or "none"),
        ("same design as", code(ref["same_design_as"]) if ref["same_design_as"] else '<span class="muted">–</span>'),
        ("recorded", "no: the checker's run details (build time, axioms, the post-synthesis vectors) are kept for "
                     "recorded designs only"),
        ("downloads", " ".join(page.link(rel_link(here, base + ext), code(ref["stem"] + ext)) for ext in (".sv", ".lean"))),
    ]), tag="section", id_="reference", title_html="The reference")
    sources = sources_card(s, sv_text, lean_text, posixpath.basename(ref["sv"]), posixpath.basename(ref["lean"]),
                           ref["sv"], ref["lean"], ref["proof_lines"], [(base + ".sv", "download")])
    reproduce = page.card(dual(reproduce_html(s), reproduce_asap7_html(s7)), tag="section", id_="reproduce",
                          title_html="Reproduce")
    body = head + detail_layout(overview, sources, [netlist], [facts], [plot, reproduce])
    site.page(here, f"{t.name} reference {ref['stem']}", body, scripts=("charts.js",), scores=True,
              description=f"svGolf {t.name}: the proved reference {ref['stem']}")


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
    how far under par. The whole card links to the task. No badges (decided 2026-11-06): only a task that
    is not open for submissions says its status, and a preview that it is not ranked."""
    tags = ("" if t.task.get("status") == "ready" and not t.preview
            else f'<div class="tags">{status_badge(t.task, t.listing)}</div>')
    return (f'<li class="task-card"><div class="task-card-top"><span class="task-no">{esc(t.number)}</span>'
            f'<span class="label">{esc(KIND_SHORT.get(t.kind, t.kind))} · {code(t.name)}</span></div>'
            f'<h3>{page.link(rel_link(here, t.page), esc(t.title))}</h3>'
            + (f"<p>{esc(t.subtitle)}</p>" if t.subtitle else "")
            + f'{tags}' + (preview_html(t) if t.preview else both(t, lambda: big_numbers(t, notes=False))) + "</li>")


def home_page(site, tasks):
    """index.html. A compact hero (title, lead, the buttons, the drawing), the task cards with the note on
    par and record under them, then home.md's FIRST `## ` section, the steps on one task as a numbered list,
    in two columns, then the rest of home.md (decided 2026-11-06: the steps after the task cards; the
    buttons in the hero, no strip of counts)."""
    here = "index.html"
    src = f"{CONTENT}/home.md"
    text = fill_home(site, tasks, read_text(src), src)
    secs = md.split_sections(text)
    lines = text.split("\n")
    if not secs or secs[0][0] != 1:
        raise BuildError(f"{src}: the home page starts with its '# ' title")
    _, title, start, _ = secs[0]
    first_h2 = next((s[2] for s in secs if s[0] == 2), len(lines))
    lead = site.render_md("\n".join(lines[start + 1:first_h2]), source=src, here=here, first_line=start + 2).html
    how = next((s for s in secs if s[0] == 2), None)
    if how is None:
        raise BuildError(f"{src}: no '## ' section: the first one is the steps on one task")
    listed = [t for t in tasks if t.listing == "listed"]
    previews = [t for t in tasks if t.preview]
    tut = [t for t in tasks if t.listing == "tutorial"]
    buttons = []
    if tut:
        buttons.append(page.button(rel_link(here, tut[0].page), "Start with the tutorial", "primary", arrow=True))
    buttons += [page.button(rel_link(here, "rules.html"), "Read the rules"),
                page.button(rel_link(here, "proving.html"), "The proving guide", "quiet")]
    if site.config.get("repo_url"):
        buttons.append(page.button(site.config["repo_url"], "The repository", "quiet"))
    head_title = md_inline(title).replace("then golf", '<span class="accent">then golf') + "</span>" \
        if "then golf" in title else md_inline(title)
    # the hero (style.css's pixel golf course), compact: the text and the buttons in the sky beside the
    # drawn green (pixelart.py, decorative)
    hero = (f'<header class="hero hero-compact"><div class="hero-sky"><div class="hero-text">'
            f'<h1>{head_title}</h1><div class="hero-lead">{lead}</div>'
            f'<div class="btn-row">{"".join(buttons)}</div></div>'
            f'<div class="hero-art">{pixelart.scene()}</div></div></header>')
    # the steps: a numbered list (step 1 in the left column, the others on the right), then what follows it
    slugger = md.Slugger(["tasks"])
    _, how_title, h0, h1 = how
    how_body = site.render_md("\n".join(lines[h0 + 1:h1]), source=src, here=here, first_line=h0 + 2).html
    if not how_body.lstrip().startswith("<ol>"):
        raise BuildError(f"{src}: the first '## ' section ({how_title}) starts with its numbered steps")
    hid = slugger.slug(how_title)
    how_body = how_body.replace("<ol>", '<ol class="how-steps">', 1)
    steps_html = (f'<section class="how" aria-labelledby="{esc(hid)}"><h2 id="{esc(hid)}">{md_inline(how_title)} '
                  f'<a class="anchor" href="#{esc(hid)}" aria-label="link to this section">#</a></h2>'
                  f'{how_body}</section>')
    def note(lib, more=""):
        return ("<strong>Par</strong> is the best proved reference that ships with the task: a design the "
                "maintainers wrote or adapted and proved, the bar to beat, never an entry. <strong>Record</strong> is "
                "the best accepted design so far; with no submissions it is par. "
                + ("Both are the one ranked number, area × time" if lib == "sky130" else
                   "In this view both are area × time, the number it orders by,")
                + f" on the {lib} cell library ({esc(combined.UNIT)}), lower is better; “–” marks a task whose "
                f"designs are not weighed on {lib} yet. <strong>Under par</strong> is how far the record is below "
                f"par, as a share of par's score (0% while par is the record).{more}")
    pre = (" <strong>Preview</strong> marks a task whose statement is still being revised: its designs are shown and "
           "measured, and its submissions are not ranked until then." if previews else "")
    notes = dual(note("sky130", pre), note("ASAP7", pre + " " + asap7_words(here, short=True)), inline=True)
    cards = "".join(task_card(t, here) for t in tut + listed + previews)
    # the library selector, on the home page beside the task cards (decided 2026-11-09: a dropdown on the front page)
    pick = ('<div class="pdk-home">' + page.pdk_select("pdk-select-home", "Golf scores on", cls="pdk-pick pdk-pick-home")
            + '<p class="pdk-what small muted">'
            + pdk_text("sky130: SkyWater's open 130 nm process, the default.",
                       "ASAP7: a predictive 7 nm library, never fabricated. "
                       + page.link(rel_link(here, f"rules.html#{ASAP7_ANCHOR}"), "How it is scored"))
            + "</p>"
            + page.pdk_nojs("The golf scores are on sky130. Seeing them on ASAP7 needs the library selector, which "
                            "needs JavaScript.", cls="pdk-nojs small muted")
            + "</div>")
    parts = [hero,
             f'<section class="course"><div class="section-head" id="tasks"><div><p class="label label-accent">'
             f'The course</p><h2>Tasks</h2></div>{pick}</div>'
             f'<ul class="task-cards">{cards}</ul><p class="course-note">{notes}</p></section>',
             steps_html]
    # the rest of home.md: a section that is a numbered list as cards, any other as a card
    for level, sec_title, s0, s1 in secs:
        if level != 2 or (level, sec_title, s0, s1) == how:
            continue
        body = site.render_md("\n".join(lines[s0 + 1:s1]), source=src, here=here, first_line=s0 + 2).html
        sid = slugger.slug(sec_title)
        head = (f'<div class="section-head"><h2 id="{esc(sid)}">{md_inline(sec_title)} <a class="anchor" '
                f'href="#{esc(sid)}" aria-label="link to this section">#</a></h2></div>')
        if body.lstrip().startswith("<ol>"):
            parts.append(head + body.replace("<ol>", '<ol class="loop">', 1))
        else:
            parts.append(head + page.card(body))
    site.page(here, site.config["site_name"], "\n".join(parts), active="index.html", scores=True,
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
    slugger = md.Slugger(["checker-stages", RATING_BUILD_ANCHOR])
    secs = doc_sections(text, cfg["sections"], site.config.get("omit", {}).get(src, []))
    parts, toc = [], []
    for title, fragment, first in secs:
        r = site.render_md(fragment, source=src, here=here, first_line=first, slugger=slugger)
        parts.append(f"<section>{r.html}</section>")
        toc.append((r.headings[0][2], r.headings[0][1]))
        if title == cfg.get("rating_build_after"):
            parts.append(rating_build_html())
            toc.append((RATING_BUILD_ANCHOR, "The build ratings use"))
        if title == cfg["stages_after"]:
            parts.append('<section><h2 id="checker-stages">The checker\'s stages <a class="anchor" '
                         'href="#checker-stages" aria-label="link to this section">#</a></h2>'
                         "<p><code>check.py</code> runs the stages in this order and stops at the first that "
                         "refuses; the stage is what a rejection names. The table is the refusal register's text, which "
                         "calls proglib by its former name, lean-surfaces.</p>" + stages_table(refusals) + "</section>")
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
                "function of the design's text, the pinned flow and tool build, the pins and the task's scoring point and input "
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
    parts.append('<h2 id="more">Where to read more</h2><p>Paths in the proglib repository:</p><ul>'
                 + "".join(f"<li>{code(x['path'])}: {md_inline(x['what'])}</li>" for x in sg["links"]) + "</ul>")
    toc += [("ls-sv", "The language tier"), ("lifting", "Lifting a refusal"), ("limits", "Known limits")]
    body = (page.page_head(title_html="What the checker refuses, and what you can write",
                           sub_html=f"Rendered from the refusal register {code(src)} (version {esc(d.get('version'))}) of "
                                    "proglib, the repository formerly named lean-surfaces, as the register's own text still "
                                    "calls it.")
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
                                                                 "definition": "sky130 area (um^2) x time (ns)"},
            "asap7": asap7_summary(t)}


def asap7_summary(t):
    """The ASAP7 view of a task for data/site.json (decided 2026-11-09; sky130 is the default and the rest of the
    summary): par, the best record and the headline as the selector's ASAP7 view shows them, and where the columns
    are."""
    with t.view("asap7"):
        best, best_time = t.best()                # the ASAP7 board's ranking[0], as task_summary's sky130 `best`
        par = t.par["score"] if t.par else None
        pm = (par_design(t) or {}).get("m") or {}
        return {"ranked_axes": list(lb.ASAP7_RANKED_AXES), "columns": f"leaderboard/asap7/{t.name}.json",
                "input_drive": (t.a7_table or {}).get("identity", {}).get("input_drive"),
                "par": None if not par else {"design": t.par["stem"], "area_um2": pm.get("area_um2"),
                                             "time_ps": pm.get("time_ps"), "area_mge": par["area_mge"],
                                             "depth": par["depth"]},
                "best": None if not best else {"record_hash": best["record_hash"], "area_e5um2": best["area_e5um2"],
                                               "time_ps": best["time_ps"], "best_time_ps": best_time,
                                               "area_mge": best["area_mge"], "depth": best["depth"]},
                "score": {k: v for k, v in headline(t).items() if not k.endswith("_design")}
                         | {"unit_ascii": combined.UNIT_ASCII, "definition": "ASAP7 area (um^2) x time (ns)"}}


def task_data(t, reference_player):
    keep = ("name", "title", "status", "kind", "top", "parameters", "ports", "statement", "banlist", "scoring",
            "allowed_axioms", "time_limit_s")
    return {"schema": SCHEMA, "task": without_comment_keys({k: t.task[k] for k in keep if k in t.task}),
            "display": {"title": t.title, "subtitle": t.subtitle}, "listing": t.listing,
            "ranked": not t.preview, "preview_note": t.preview_note,
            "reference_player": reference_player,
            "board": None if t.preview else t.full_board, "submissions_board": None if t.preview else t.board,
            "asap7": None if t.preview else {
                "board": t.states["asap7"]["full_board"], "submissions_board": t.states["asap7"]["board"],
                "par": (t.states["asap7"]["par"] or {}).get("stem"), "columns": f"leaderboard/asap7/{t.name}.json"},
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
    v = prerequisites(site)
    how = (f"Records are made locally with leaderboard/leaderboard.py (written to leaderboard/data/<task>/, the "
           f"directory a pull request adds) and handed in by pull request to {repo_url}." if repo_url else
           "Public submissions open when the svGolf repository is published; until then, records are made "
           "locally with leaderboard/leaderboard.py (written to leaderboard/data/<task>/).")
    clone = []
    if repo_url:
        top = posixpath.basename(repo_url.rstrip("/"))
        top = top[:-len(".git")] if top.endswith(".git") else top
        clone = [f"git clone {repo_url}", f"cd {top}" + ("/svgolf" if LAYOUT == "inside" else "")]
    example = next((t for t in tasks if t.name == "add"), tasks[0] if tasks else None)
    goal_const = example.task["statement"]["constant"] if example else "<the task's statement constant>"
    clocked = next((t for t in tasks if metrics.is_clocked(t.task)), None)     # a listed clocked task, if any
    latency_tasks = [t for t in tasks if metrics.has_latency(t.task)]           # whose Goal takes the latency
    clocked_lines = ([f"# a clocked task ({clocked.name}) is weighed through the clocked flow, its time the period:",
                      f"# python3.12 score/ppa.py solution.sv --task tasks/{clocked.name} --seq --path"]
                     if clocked else [])
    # check.py refuses an --unproved run of a latency kind without --latency (a usage error, exit 2)
    lat_ex = next((t for t in latency_tasks if unproved_latency(t).isdigit()),
                  latency_tasks[0] if latency_tasks else None)
    latency_lines = ([f"# on a task with a latency ({', '.join(t.name for t in latency_tasks)}), --unproved needs --latency n, "
                      "the cycles you mean to claim (the n of your `-- svgolf-latency: n` line; check.py refuses the run "
                      f"without it), e.g. par's on {lat_ex.name}:",
                      f"# python3.12 check.py tasks/{lat_ex.name} solution.sv --unproved --latency {unproved_latency(lat_ex)}"]
                     if lat_ex else [])
    lines = ["# svGolf", "",
             "> A competition for SystemVerilog hardware: write a "
             + (f"circuit (combinational, or clocked on a clocked task such as `{clocked.name}`)" if clocked else
                "combinational circuit")
             + ", prove in Lean 4 that it meets a task's trusted statement, and get scored by "
             "a pinned flow. The one ranked number is area x time on the sky130 cell library (flow A0'): the cell "
             "area in um^2 (flip-flops included) times the critical-path delay (on a clocked task, the "
             "register-to-register clock period, times the latency in cycles where the task has one), in um2*ns, "
             "lower is better. Par, Record and Under par use "
             "it; to beat par is to be accepted with a smaller area x time than the task's best proved reference. "
             "The Pareto front of area and time, area in NAND2 gate equivalents (GE), depth in gates and the other "
             "flows are exploration columns. [Reproduce a score](reproduce.html) says how to get the same numbers. "
             "sky130 is the default; the site can also show every golf score on ASAP7, a predictive 7 nm library "
             "(the same netlists weighed by score/ppa.py --pdk asap7; leaderboard.py board --pdk asap7; data/site.json "
             "`asap7`; [the rules](rules.html#" + ASAP7_ANCHOR + ") say how).",
             "",
             f"All paths below are relative to this file. There is no submission server. {how} Par, the bar to "
             f"beat, is a task's best proved reference; the records of {site.config['reference_player']} are the "
             "references, not entries. [llms-full.txt](llms-full.txt) is the whole proving guide in plain text.", "",
             "## Step 0, once per machine", "",
             f"Install elan (it installs the Lean toolchain that lean-toolchain pins, {v['lean']}), Yosys "
             f"{v['yosys']} with yosys-abc, Verilator 5, a C++ compiler and make (the post-synthesis check compiles "
             "Verilator's model of the netlist) and Python 3.12. Then, from the root of a clone:", "",
             "```bash", *clone,
             "python3.12 -m pip install -r requirements.txt   # " + v["pyslang"],
             "lake build                                      # the trusted Lean and the checker's evaluator",
             "python3.12 score/ppa.py --fetch-liberty         # the pinned sky130 liberty, checked by its hash",
             "```", "",
             f"`lake build` takes {LAKE_BUILD_COST}.", "",
             "## The commands (task `add`; any task: tasks/<name>)", "",
             "```bash",
             "# the golfing inner loop: the ranked area and delay in about 2 s, no Lean (--path: the critical path)",
             "python3.12 score/ppa.py solution.sv --task tasks/add --no-mapped --path",
             *clocked_lines,
             "# 1. no proof needed: every stage but the proof; never accepts; exits 0 when every stage passed",
             "python3.12 check.py tasks/add solution.sv --unproved",
             *latency_lines,
             "# 2. the real check: prints \"accepted\": true; its post-synthesis check is LIGHT by default (a subset "
             "of the vectors, for local feedback), so stderr also says \"accepted, but the check was INCOMPLETE ... "
             "rerun with --postsynth full\": expected, since step 3 runs the full one itself",
             "python3.12 check.py tasks/add solution.sv Solution.lean",
             "# 3. record it (the whole check again, full mode, OS sandbox); --data-dir DIR for a private trial",
             "python3.12 leaderboard/leaderboard.py add --task add --player YOUR_HANDLE --assisted-by \"TOOL OR MODEL\" "
             "--sv solution.sv --lean Solution.lean",
             "```", "",
             "score/ppa.py runs the source gate and the pinned flow and prints ppa.area_um2_sky130 and "
             "ppa.delay_ps_sky130 (their product is the ranked number). It does not check the banlist, the 4-state "
             "rules, whether ls-sv can read the design, the post-synthesis simulation or the task's function, and "
             "needs no proof: step 1 must still pass before you prove. Every run of check.py that reaches its ppa "
             "stage ends its stderr with the ranked headline `ranked (sky130 A0'): <area> um^2 x <delay> ps = <axt> "
             "um2*ns; par <par axt> (<par ref>)`, or `ranked: liberty missing, run python3.12 score/ppa.py "
             "--fetch-liberty`.", "",
             "## The Lean contract", "",
             "A submission is two files, here solution.sv (the task's exact module header) and Solution.lean; names "
             "and paths are free. The checker extracts the .sv itself and generates the trusted module "
             "Submission.Design:", "",
             "```lean",
             *design_module(example).rstrip("\n").split("\n"),
             "```", "",
             "Solution.lean must `import Submission.Design` and, inside `namespace Submission`, prove "
             "`theorem solution : Goal` (that is `theorem Submission.solution : Submission.Goal`); Goal unfolds to "
             f"the task's statement of the design, `{goal_const} Submission.design.sem` for add. The module name, "
             "the import and the theorem are fixed. "
             + (f"On a task with a latency ({and_list([f'`{t.name}`' for t in latency_tasks])}), Goal takes the "
                "solution's latency: Solution.lean also defines `lat` (cycles, one Nat per parameter, in the task's "
                "order), proves `theorem solution : Goal lat`, which unfolds to the statement of `design.sem lat` and "
                "`lat <scoring point> = n`, and declares that n in exactly one line `-- svgolf-latency: n`; the "
                "score's time is n times the clock period. " if latency_tasks else "")
             + "Allowed imports: Init, Std, Lean, LeanModels.Sv.*, SvGolf.*, "
             "tasks.*, and Mathlib with its packages; axioms: the task's allowed_axioms (normally propext, "
             "Classical.choice, Quot.sound); no sorry, native_decide or bv_decide. Every task ships a complete "
             "reference pair under tasks/<name>/reference/.", "",
             "## Pages", "",
             "- [Tasks and scorecard](index.html)",
             "- [The tutorial: your first submission, step by step](tasks/_example/index.html#first-submission)",
             "- [Rules, checker stages, scoring, leaderboard](rules.html)",
             "- [Reproduce a score: the pinned tools, files and commands](reproduce.html)",
             "- [How to prove a task](proving.html) ([plain text](llms-full.txt))",
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
        clocked_note = ((" Clocked: weigh it with `score/ppa.py --seq`; its time is the register-to-register clock "
                         "period" + (", times its latency in cycles (the solution's `-- svgolf-latency: n` line); "
                                     f"`check.py --unproved` needs `--latency n` on it (par's n: "
                                     f"{unproved_latency(t)})." if metrics.has_latency(t.task) else
                                     ", one decision per cycle.")) if metrics.is_clocked(t.task) else "")
        lines.append(f"- [{t.title}]({t.page}) (`{t.name}`): {t.subtitle}{clocked_note} Scored at {point_text(t.point)}; "
                     f"{par}; {best}. Statement: `{t.task['statement']['constant']}`. Data: "
                     f"[{s['data']}]({s['data']}).{statement}")
    lines += ["", "## Data", "",
              "- [data/site.json](data/site.json): every task's par, best submission and counts",
              "- data/tasks/<task>.json: leaderboard.py's board of every record (`board`), the players' board "
              "(`submissions_board`), references, baselines, rejected designs, the statement's import closure "
              "and its properties (`properties`: each one's Lean declaration, file, line and plain-English text)", ""]
    return "\n".join(lines)


def llms_full_txt(site):
    """The proving guide (PROVING.md, config.json's redactions applied) as one plain-text file, for a reader
    that cannot take the whole of proving.html at once."""
    cfg = site.config["pages"]["proving"]
    text = omit_sections(site.doc_text(cfg["source"]), site.config.get("omit", {}).get(cfg["source"], []))
    return ("# svGolf: the proving guide, in plain text\n\n"
            "> The Markdown source of proving.html. The site's index for agents is llms.txt.\n\n" + text)


def machine_outputs(site, tasks):
    site.add("data/site.json", json_text({"schema": SCHEMA, "revision": site.revision, "flow": site.flow,
                                          "reference_player": site.config["reference_player"],
                                          "tasks": [task_summary(t) for t in tasks]}))
    for t in tasks:
        site.add(f"data/tasks/{t.name}.json", json_text(task_data(t, site.config["reference_player"])))
    site.add("llms.txt", llms_txt(site, tasks))
    site.add("llms-full.txt", llms_full_txt(site))


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
    ge_tables = load_ge_tables()
    site.add("style.css", read_bytes("svgolf/site/style.css"))
    site.add("site.js", read_bytes("svgolf/site/site.js"))
    site.add("charts.js", read_bytes("svgolf/site/charts.js"))
    site.add("pdk.js", read_bytes("svgolf/site/pdk.js"))
    home_page(site, tasks)
    for t in tasks:
        task_page(site, t)
        for rec in t.records:
            record_page(site, t, rec, ge_tables)
        for ref in t.refs:
            if not ref["record_hash"] and not t.preview:      # a preview has no detail pages (reference_page)
                reference_detail_page(site, t, ref, ge_tables)
        licence_texts(site, t)
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
