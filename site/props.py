"""The properties panel of a task page: the trusted statement, one card per property a circuit
must have, and the definitions those properties use.

Inputs, both in the task's directory: `properties.json` (each property's name, declaration, file
and plain-English paragraph; the definitions; the theorem that ties them to the statement) and
`Properties.lean` (the properties as Lean definitions and `statement_iff_properties`, proved, not
trusted). The Lean text of every card is cut from its file by declaration name (leansrc.py),
VERBATIM, never copied into the JSON, so a card cannot drift from the file.

`load` reads and checks them (each fatal, a BuildError): the JSON names this task's
Properties.lean, its statement is the task's trusted constant, every declaration it names is
declared in the file it names, every file is this task's Properties.lean or a module of the
statement's trusted import closure, and the theorem's statement names every property. `panel`
renders the two tabs, PROPERTIES and DEFINITIONS (site.js makes them tabs; without JavaScript
they are two sections, one under the other), the counters, the cards, and the line that says
the cards are exactly the statement, with links to the source views.
"""

import json
import posixpath

import leansrc
import page
from page import esc, code


class PropsError(Exception):
    """properties.json or Properties.lean does not say what the panel needs."""


class Entry:
    """A property or a definition, resolved: its JSON fields, its declaration in its file, the
    verbatim Lean text, the docstring as one line, and where the source view shows it."""

    def __init__(self, item, decl, text, source):
        self.name, self.decl, self.file = item["name"], item["decl"], item["file"]
        self.kind = item.get("kind", "definition")
        self.text = item["text"]
        self.line = decl.start + 1
        self.lean = leansrc.excerpt(text, decl)
        self.doc = docstring(self.lean)
        self.source = source                      # a site path with a #fragment

    @property
    def short(self):
        return self.decl.rsplit(".", 1)[-1]


class TaskProperties:
    """A task's properties.json, resolved against the files it names."""

    def __init__(self, info, entries, definitions, theorem, statement, file, module):
        self.info, self.properties, self.definitions = info, entries, definitions
        self.theorem, self.statement, self.file, self.module = theorem, statement, file, module

    @property
    def summary(self):
        return self.info.get("summary", "")


def docstring(lean_text):
    """The doc comment that opens a declaration's text, as one line, or ""."""
    s = lean_text.lstrip()
    if not s.startswith("/--"):
        return ""
    end = s.find("-/")
    return " ".join(s[3:end].split()) if end > 0 else ""


def load(task_name, task_dir, statement_constant, closure, read_text, source_page, exists):
    """The task's TaskProperties, or None when the task has no properties.json.

    `closure`: [(module, repository path or None)], the statement's trusted import closure;
    `source_page(repo_path, decl_name)`: the site path (with fragment) where the declaration is
    shown; `read_text(repo_path)`, `exists(repo_path)`: the repository."""
    rel = f"{task_dir}/properties.json"
    if not exists(rel):
        return None
    try:
        info = json.loads(read_text(rel))
    except ValueError as e:
        raise PropsError(f"{rel}: not JSON: {e}")
    file = f"{task_dir}/Properties.lean"
    where = f"{rel}"
    if info.get("file") != file:
        raise PropsError(f"{where}: `file` is {info.get('file')!r}, not this task's {file}")
    if not exists(file):
        raise PropsError(f"{where}: {file} does not exist")
    stmt = info.get("statement") or {}
    if stmt.get("decl") != statement_constant:
        raise PropsError(f"{where}: the statement is {stmt.get('decl')!r}, but task.json's is {statement_constant!r}")
    trusted = {p for _, p in closure if p}
    texts, indexes = {}, {}

    def resolve(item, what):
        for key in ("name", "decl", "file", "text"):
            if not isinstance(item.get(key), str) or not item[key].strip():
                raise PropsError(f"{where}: {what} {item.get('name')!r} has no {key!r}")
        path = item["file"]
        if path != file and path not in trusted:
            raise PropsError(f"{where}: {what} {item['name']}: {path} is neither {file} nor trusted text of the "
                             "statement (its import closure), so the site does not show it")
        if path not in texts:
            texts[path] = read_text(path)
            indexes[path] = {d.name: d for d in leansrc.declarations(texts[path])}
        decl = indexes[path].get(item["decl"])
        if decl is None:
            raise PropsError(f"{where}: {what} {item['name']}: {path} declares no {item['decl']}")
        return Entry(item, decl, texts[path], source_page(path, item["decl"]))

    props = [resolve(p, "property") for p in info.get("properties", [])]
    if not props:
        raise PropsError(f"{where}: no properties")
    for p in props:
        if p.file != file:
            raise PropsError(f"{where}: property {p.name} is declared in {p.file}, not in {file}")
        if p.kind not in ("range", "property"):
            raise PropsError(f"{where}: property {p.name}: kind {p.kind!r} is neither 'range' nor 'property'")
    defs = [resolve(d, "definition") for d in info.get("definitions", [])]
    theorem = resolve({"name": "statement_iff_properties", "decl": info.get("theorem"), "file": file,
                       "text": "the theorem"}, "theorem")
    sig = leansrc.signature(texts[file], indexes[file][theorem.decl])
    for p in props:
        if p.short not in sig:
            raise PropsError(f"{where}: the theorem {theorem.decl} does not mention the property {p.name} ({p.short})")
    statement = resolve({"name": "Statement", "decl": stmt["decl"], "file": stmt.get("file", ""),
                         "text": "the statement"}, "statement")
    theorem.signature = sig
    module = posixpath.splitext(file)[0].split("/", 1)[1].replace("/", ".")   # tasks.<t>.Properties
    return TaskProperties(info, props, defs, theorem, statement, file, module)


# ---------------------------------------------------------------------------
# the panel
# ---------------------------------------------------------------------------

def _path_row(e, link):
    return (f'<div class="prop-path"><span>{esc(page.shown_path(e.file))}:{e.line}</span>'
            + page.button(link(e.source), "Open in code", "quiet sm", arrow=True) + "</div>")


def property_card(e, *, proved, link, md_inline):
    """One property: its name, a badge, the docstring as a one-line gist; opened, the paragraph,
    the Lean definition, the file and line, the source view. `proved=None` is a TASK's page: a
    property there is a requirement, so it carries no proof status (only the range card is badged);
    True/False are for a solution's page, where each property is proved by that solution or not."""
    if e.kind == "range":
        status, status_text = "plain", "range"
    elif proved is None:
        status, status_text = None, None
    else:
        status, status_text = ("proved", "proved") if proved else ("todo", "to prove")
    body = (f"<p>{md_inline(e.text)}</p>"
            + page.code_block(e.lean, "lean", name=e.short, cls="code excerpt")
            + _path_row(e, link))
    return page.prop_card(e.name, status=status, status_text=status_text, gist_html=md_inline(e.doc) if e.doc else None,
                          body_html=body, id_=f"prop-{e.name}")


def definition_card(e, *, link, md_inline):
    """One definition: its name, the file it is in (the group it stands in says whether that is
    trusted), its sentence; opened, the Lean text, the file and line, the source view."""
    body = page.code_block(e.lean, "lean", name=e.short, cls="code excerpt") + _path_row(e, link)
    return page.prop_card(e.name, status="file", status_text=posixpath.basename(e.file),
                          gist_html=md_inline(e.text), body_html=body, id_=f"def-{e.decl}")


def panel(tp, *, task_dir, proved, rejected, link, md_inline, rejected_href="#does-not-count", extra_panes=(),
          title_tag="p"):
    """The panel. `proved`: None on a task's page (requirements, no proof status); on a solution's
    page, whether that solution's proof is accepted (so every property holds of it); `rejected`: how many wrong designs and attacks the checker rejects (the counter links to
    them; 0 draws no counter: the task page shows them in a tab of their own); `link(site path)`: a relative link
    from the page; `extra_panes`: more tabs after Properties and Definitions, (id, label, count, HTML) each;
    `title_tag`: the panes' titles' tag (page.props_panel)."""
    n_props = sum(1 for p in tp.properties if p.kind == "property")
    cards = [property_card(p, proved=proved, link=link, md_inline=md_inline) for p in tp.properties]
    ranges = [p for p in tp.properties if p.kind == "range"]
    summary = tp.summary.replace(tp.theorem.short, f"`{tp.theorem.short}`") if "`" not in tp.summary else tp.summary
    th = tp.theorem
    intro_html = md_inline(summary) if summary else ""
    # the theorem's name in the summary links to the theorem (the proof that the cards are exactly
    # the trusted statement); that sentence is the only place the panel explains it
    intro_html = intro_html.replace(f"<code>{esc(th.short)}</code>", page.link(link(th.source), code(th.short)), 1)
    intro = f'<p class="props-intro">{intro_html}</p>' if intro_html else ""
    if ranges:
        intro += ('<p class="props-intro small muted">'
                  + ", ".join(code(p.name) for p in ranges)
                  + " is the range the statement covers, not a property: every other card must hold at "
                    "each value in it.</p>")
    props_body = intro + '<div class="prop-list">' + "".join(cards) + "</div>"
    # the definitions: this task's trusted text, the helpers of Properties.lean, the shared base
    groups = (("own", "This task's trusted text", lambda e: e.file.startswith(task_dir + "/") and e.file != tp.file),
              ("helper", "Helpers in Properties.lean (proved, not trusted)", lambda e: e.file == tp.file),
              ("shared", "The shared trusted base", lambda e: not e.file.startswith(task_dir + "/")))
    defs_body = ('<p class="props-intro">The names the properties use, each with its Lean text. Trusted text '
                 "is what a proof is about; a helper of Properties.lean is not trusted: Lean checks it as part of "
                 + page.link(link(th.source), code(th.short)) + ".</p>")
    for _, title, member in groups:
        mine = [d for d in tp.definitions if member(d)]
        if mine:
            defs_body += (f'<p class="label props-group">{esc(title)}</p><div class="prop-list">'
                          + "".join(definition_card(d, link=link, md_inline=md_inline) for d in mine) + "</div>")
    counts = []
    if proved is True:
        counts.append(page.Counter(f"Proved {n_props}", "proved",
                                   title="this solution has each property: the checker accepted its proof"))
    elif proved is False:
        counts.append(page.Counter(f"To prove {n_props}", "todo", title="this solution's proof is not accepted"))
    if rejected:
        counts.append(page.Counter(f"Attacks rejected {rejected}", "rejected", href=rejected_href,
                                   title="wrong designs and attacks the checker rejects: what does not count"))
    return page.props_panel(
        [("props-properties", "Properties", n_props, props_body),
         ("props-definitions", "Definitions", len(tp.definitions), defs_body)] + list(extra_panes),
        counters=counts, hook="properties", title_tag=title_tag)
