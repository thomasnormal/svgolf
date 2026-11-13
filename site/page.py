"""HTML building blocks of the svGolf site: escaping, the page layout, and the
components of the design system (style.css): the page head with its big
stats, cards, small-caps labels, buttons, badges, code blocks, tables,
the leaderboard list, property cards, the document layout. (Not `html.py`:
that would shadow the standard library's `html` module for every file in this
directory.)

Every function returns a string of HTML. Arguments named `*_html` (and the
cells of `table`) are already HTML; everything else is text and is escaped
here. Pages read without JavaScript: site.js only adds the copy buttons of
code blocks and the property panel's tabs.
"""

import html
import re

import pixelart
from highlight import highlight, language_of

_TAG = re.compile(r"<[^>]*>")

NAV = (("index.html", "Tasks"), ("rules.html", "Rules"), ("proving.html", "Proving"),
       ("refusals.html", "Refusals"), ("about.html", "About"))


def esc(s):
    return html.escape(str(s), quote=True)


def shown_path(rel):
    """A repository path as the public repository shows it (decided 2026-11-11): svGolf's own files, written
    `svgolf/...` in this tree (lean-surfaces' layout), lose the prefix, since the public repository is svGolf's tree
    itself; any other path (the Lean library's) is unchanged."""
    return rel[len("svgolf/"):] if rel.startswith("svgolf/") else rel


class Html(str):
    """Text that is already HTML (a table head with markup in it)."""


def code(s):
    """Inline code."""
    return f"<code>{esc(s)}</code>"


def link(href, text_html, cls=None):
    c = f' class="{cls}"' if cls else ""
    return f'<a href="{esc(href)}"{c}>{text_html}</a>'


def badge(text, kind):
    """A small pill label; `kind` picks its style and its identity dot (open, draft, par,
    reference, baseline, frontier, banned, proved, refuted, ...)."""
    return f'<span class="badge badge-{esc(kind)}">{esc(text)}</span>'


def label(text_html, *, accent=False, tag="p", id_=None):
    """A small-caps section label ("THIS TASK", "SUBMIT")."""
    cls = "label label-accent" if accent else "label"
    i = f' id="{esc(id_)}"' if id_ else ""
    return f'<{tag} class="{cls}"{i}>{text_html}</{tag}>'


def button(href, text_html, kind="outline", *, arrow=False, download=False):
    """A link styled as a button: `primary` (filled accent), `outline` (accent outline), `quiet`
    (ink outline); `sm` may be added (`"quiet sm"`)."""
    cls = "btn" + "".join(f" btn-{k}" for k in kind.split() if k != "outline")
    tail = ' <span class="arrow" aria-hidden="true">→</span>' if arrow else ""
    dl_ = " download" if download else ""
    return f'<a class="{cls}" href="{esc(href)}"{dl_}>{text_html}{tail}</a>'


def code_block(text, lang=None, *, src=None, cls="code", name=None, actions_html="", term=False, body_html=None):
    """A highlighted, verbatim block. `src` (a repository path) marks a block
    that reproduces a file byte for byte: `data-src` names it. With a `name`
    (a file name, a language) or `actions_html` (download links), the block
    gets a head; `term` draws it as a terminal. `body_html`, already rendered,
    replaces the highlighting of `text` (leansrc.anchored_html: a source view
    with an anchor per line). site.js adds a copy button to every block."""
    lang = language_of(lang) if lang else None
    attrs = f' class="{cls}"'
    if lang:
        attrs += f' data-lang="{esc(lang)}"'
    if src:
        attrs += f' data-src="{esc(src)}"'
    if body_html is not None:
        body = body_html
    else:
        body = highlight(text, lang) if lang else html.escape(text, quote=False)
    pre = f"<pre{attrs}><code>{body}</code></pre>"
    if not (name or actions_html or term):
        return pre
    head = ""
    if name or actions_html:
        head = (f'<div class="codebox-head"><span class="codebox-name">{esc(name or "")}</span>'
                f'<span class="codebox-actions">{actions_html}</span></div>')
    return f'<div class="codebox{" term" if term else ""}">{head}{pre}</div>'


def details(summary_html, body_html, cls=None, id_=None):
    """A collapsed block (no JavaScript: the browser's own disclosure); site.js opens it when a link or the URL's
    fragment names it or something inside it."""
    c = (f' class="{cls}"' if cls else "") + (f' id="{esc(id_)}"' if id_ else "")
    return f"<details{c}><summary>{summary_html}</summary>\n{body_html}\n</details>"


def table(headers, rows, *, numeric=(), cls=None, caption_html=None, stack=False):
    """A table in a horizontally scrolling wrapper. `headers` are text (or Html);
    each row is a list of cell HTML, or a Row when its `<tr>` needs a class
    or an id; `numeric` lists the right-aligned column indexes. `stack`: on a
    phone each row becomes a small card, its first cell on top and every other
    cell under its column's name (style.css `table.stack`; each cell carries
    the name as `data-label`), instead of a table that scrolls sideways."""
    num = set(numeric)
    right = ' class="num"'
    head = "".join(f'<th{right if k in num else ""} scope="col">{h if isinstance(h, Html) else esc(h)}</th>'
                   for k, h in enumerate(headers))
    names = [html.unescape(_TAG.sub("", h)) if isinstance(h, Html) else str(h) for h in headers]
    body = []
    for r in rows:
        tr_attr = ""
        if isinstance(r, Row):
            tr_attr, r = r.attrs, r.cells
        tds = "".join(f'<td{right if k in num else ""}'
                      + (f' data-label="{esc(names[k])}"' if stack and k < len(names) else "") + f">{c}</td>"
                      for k, c in enumerate(r))
        body.append(f"<tr{tr_attr}>{tds}</tr>")
    cap = f"<caption>{caption_html}</caption>" if caption_html else ""
    if stack:
        cls = f"{cls} stack" if cls else "stack"
    elif len(headers) >= 5:
        cls = f"{cls} wide" if cls else "wide"   # many columns: scrolls on a phone (style.css)
    c = f' class="{cls}"' if cls else ""
    return (f'<div class="table-wrap"><table{c}>{cap}<thead><tr>{head}</tr></thead>'
            f"<tbody>\n" + "\n".join(body) + "\n</tbody></table></div>")


class Row:
    """A table row with attributes on its `<tr>` (e.g. a class)."""

    def __init__(self, cells, cls=None, id_=None):
        self.cells = cells
        self.attrs = (f' class="{esc(cls)}"' if cls else "") + (f' id="{esc(id_)}"' if id_ else "")


def dl(pairs):
    """A definition list from (term, value_html) pairs."""
    items = "".join(f"<dt>{esc(k)}</dt><dd>{v}</dd>" for k, v in pairs)
    return f'<dl class="facts">{items}</dl>'


def toc(entries, label_text="On this page"):
    """An in-page table of contents from (anchor id, text_html) pairs."""
    items = "".join(f'<li><a href="#{esc(i)}">{t}</a></li>' for i, t in entries)
    return f'<nav class="toc" aria-label="{esc(label_text)}"><ul>{items}</ul></nav>'


# ---------------------------------------------------------------------------
# the page head, stats, cards
# ---------------------------------------------------------------------------

class Stat:
    """One big number: `value` over a small-caps `label`, with an optional `unit` after the value
    and a `note` under it. `kind` styles it: good, accent, empty. `icon_html`: a decorative drawing
    (pixelart.icon, aria-hidden) beside the number. `label_href`: the label is a link there (where the
    page defines the term)."""

    def __init__(self, label, value, *, unit=None, note=None, kind=None, icon_html=None, label_href=None):
        self.label, self.value, self.unit, self.note, self.kind = label, value, unit, note, kind
        self.icon_html, self.label_href = icon_html, label_href

    def html(self):
        k = f" stat-{esc(self.kind)}" if self.kind else ""
        unit = f'<span class="unit">{esc(self.unit)}</span>' if self.unit else ""
        note = f'<span class="stat-note">{esc(self.note)}</span>' if self.note else ""
        ico = self.icon_html or ""
        label = link(self.label_href, esc(self.label)) if self.label_href else esc(self.label)
        return f'<div class="stat{k}"><dt>{label}</dt><dd>{ico}{esc(self.value)}{unit}{note}</dd></div>'


def stats(items, *, cls=None):
    """A row of big numbers (Stat objects)."""
    c = f" {cls}" if cls else ""
    return f'<dl class="stats{c}">' + "".join(s.html() for s in items) + "</dl>"


def page_head(*, title_html, crumbs_html=None, number=None, sub_html=None, tags_html=None,
              aside_html=None, lead_html=None):
    """The head of a page: breadcrumbs, an optional accent number, the title (an `<h1>`), a
    subtitle, tags (badges), a lead paragraph, and on the right `aside_html` (the big stats).
    A heavy rule closes it, the fairway, with the flag in its hole at the end (pixelart, decorative)."""
    crumbs = f'<p class="crumbs">{crumbs_html}</p>' if crumbs_html else ""
    no = f'<span class="task-no" aria-hidden="true">{esc(number)}</span>' if number is not None else ""
    sub = f'<p class="head-sub">{sub_html}</p>' if sub_html else ""
    tags = f'<p class="head-tags">{tags_html}</p>' if tags_html else ""
    lead = f'<div class="head-lead">{lead_html}</div>' if lead_html else ""
    aside = aside_html or ""
    return (f'{crumbs}<header class="page-head"><div class="head-main"><div class="title-row">{no}'
            f"<h1>{title_html}</h1></div>{sub}{tags}{lead}</div>{aside}{pixelart.hole_flag()}</header>")


def card(body_html, *, tag="div", id_=None, cls=None, label_html=None, title_html=None, title_id=None,
         actions_html=None, flush=False, foot_html=None):
    """A card: an optional head (a small-caps label or a title, with actions on the right), the
    body, an optional foot. `flush` drops the padding (for lists that run to the edges)."""
    classes = "card" + (" card-flush" if flush else "") + (f" {cls}" if cls else "")
    i = f' id="{esc(id_)}"' if id_ else ""
    head = ""
    if label_html or title_html or actions_html:
        tid = f' id="{esc(title_id)}"' if title_id else ""
        t = (label(label_html, accent=True) if label_html else "") + \
            (f'<h2 class="card-title"{tid}>{title_html}</h2>' if title_html else "")
        a = f'<div class="card-actions">{actions_html}</div>' if actions_html else ""
        head = f'<div class="card-head"><div>{t}</div>{a}</div>'
    foot = f'<div class="card-foot">{foot_html}</div>' if foot_html else ""
    return f"<{tag} class=\"{classes}\"{i}>{head}{body_html}{foot}</{tag}>"


def seg(options, on=0, *, label_text):
    """A segmented control (static: the option `on` is pressed). The page's script wires it."""
    items = "".join(f'<button type="button" aria-pressed="{"true" if k == on else "false"}">{esc(o)}</button>'
                    for k, o in enumerate(options))
    return f'<div class="seg" role="group" aria-label="{esc(label_text)}">{items}</div>'


def tabs(panes, *, label_text):
    """Tabs in a card (a detail page's netlist: Schematic, Critical path, Cells and, on the routed course, Layout).
    `panes`: (id, tab label, body HTML) or (id, tab label, body HTML, class): each pane is a `<section>` with that id,
    so a link to the id lands on it; a class goes on both the tab and its pane (`pdk-asap7pnr`: a tab of the routed
    course only, which style.css hides on sky130 and without JavaScript). Without JavaScript the tab links jump to the
    panes, which stand one under the other, each under its own title, and no tab is marked as chosen; site.js makes
    them tabs (the first one shown) and shows the pane a link or the URL's fragment names (or holds), and a tab chosen
    names its pane in the URL; a tab its course hides is never the one shown."""
    panes = [p if len(p) == 4 else (*p, None) for p in panes]

    def cls(c, base=""):
        names = " ".join(x for x in (base, c) if x)
        return f' class="{esc(names)}"' if names else ""
    links = "".join(f'<a href="#{esc(pid)}"{cls(c)}>{esc(label)}</a>' for pid, label, _, c in panes)
    body = "".join(f'<section{cls(c, "tabs-pane")} id="{esc(pid)}"><h3 class="tabs-pane-title">{esc(label)}</h3>'
                   f"{html_}</section>" for pid, label, html_, c in panes)
    return f'<div class="tabs" data-tabs><nav class="tabs-nav" aria-label="{esc(label_text)}">{links}</nav>{body}</div>'


# ---------------------------------------------------------------------------
# the leaderboard list, property cards
# ---------------------------------------------------------------------------

class BoardRow:
    """One row of a leaderboard: `rank` (a number, or "" for par), the name (HTML, usually a link),
    a meta line (HTML), the score (text) with a breakdown line under it, and the bar's fill as a
    fraction of the worst score shown (0..1). `kind`: lead (the record), par, or None."""

    def __init__(self, rank, name_html, meta_html, score, breakdown_html="", fill=None, kind=None):
        self.rank, self.name_html, self.meta_html, self.score = rank, name_html, meta_html, score
        self.breakdown_html, self.fill, self.kind = breakdown_html, fill, kind

    def html(self):
        k = f' class="{esc(self.kind)}"' if self.kind else ""
        bar = ""
        if self.fill is not None:
            pct = max(0.0, min(1.0, self.fill)) * 100
            bar = f'<span class="bar" aria-hidden="true"><span style="width:{pct:.1f}%"></span></span>'
        rank = esc(self.rank) if self.rank != "" else '<span aria-label="par">⚑</span>'
        small = f"<small>{self.breakdown_html}</small>" if self.breakdown_html else ""
        return (f'<li{k}><span class="board-rank">{rank}</span>'
                f'<div class="board-who"><div class="board-name">{self.name_html}</div>'
                f'<div class="board-meta">{self.meta_html}</div>{bar}</div>'
                f'<div class="board-score">{esc(self.score)}{small}</div></li>')


def board(rows, *, empty_html=None):
    """A leaderboard list (BoardRow objects); `empty_html` is shown above the rows when no player
    has an entry yet."""
    empty = f'<div class="board-empty">{empty_html}</div>' if empty_html else ""
    return empty + '<ol class="board">' + "".join(r.html() for r in rows) + "</ol>"


def prop_card(name, *, status, body_html, status_text=None, gist_html=None, id_=None, open_=False):
    """A property of a statement (or a definition it uses), folded: an UPPER_SNAKE_CASE name, a
    status badge (`status` picks its style, `status_text` its words: range, the file a definition is
    in, or proved / to prove on a solution's page; `status=None` draws no badge) and a one-line gist; unfolded, `body_html` (props.py: the plain-English paragraph, the
    Lean text in a copyable block, the file and a button into the source view). The browser's own
    disclosure: it opens without JavaScript."""
    i = f' id="{esc(id_)}"' if id_ else ""
    o = " open" if open_ else ""
    gist = f'<span class="prop-gist">{gist_html}</span>' if gist_html else ""
    return (f'<details class="prop"{i}{o}><summary><span class="prop-top"><span class="prop-name">{esc(name)}</span>'
            f'{badge(status_text or status, status) if status else ""}</span>{gist}</summary>'
            f'<div class="prop-body">{body_html}</div></details>')


class Counter:
    """A counter of the property panel's head ("Proved 4"): `kind` styles it (proved, todo,
    rejected); with an `href` it is a link."""

    def __init__(self, text, kind, *, href=None, title=None):
        self.text, self.kind, self.href, self.title = text, kind, href, title

    def html(self):
        t = f' title="{esc(self.title)}"' if self.title else ""
        if self.href:
            return f'<a class="{esc(self.kind)}" href="{esc(self.href)}"{t}>{esc(self.text)}</a>'
        return f'<span class="{esc(self.kind)}"{t}>{esc(self.text)}</span>'


def props_panel(panes, *, counters=(), hook=None, foot_html="", title_tag="p"):
    """The panel of property cards. `panes`: (id, tab label, count or None, body HTML), each a
    tab (the task page's last one is "What does not count"). Without JavaScript the tabs are links to the
    panes, which stand one under the other, each under its own title (`title_tag`: a heading's tag where the panel
    sits under one, so that heading navigation finds each pane); site.js makes them tabs (the first one shown) and
    shows the pane a link or the URL's fragment names, opening the card it names. A tab with a count is named
    "label (count)" for assistive technology, which would otherwise read the two run together."""
    on = ' class="on"'
    tabs = "".join(f'<a href="#{esc(pid)}"{on if k == 0 else ""}'
                   + (f' aria-label="{esc(label)} ({n})"' if n is not None else "") + f">{esc(label)}"
                   + (f'<span class="props-n">{n}</span>' if n is not None else "") + "</a>"
                   for k, (pid, label, n, _) in enumerate(panes))
    counts = "".join(c.html() for c in counters)
    body = "".join(f'<div class="props-pane" id="{esc(pid)}"><{title_tag} class="props-pane-title">{esc(label)}'
                   f'</{title_tag}>{html_}</div>'
                   for pid, label, _, html_ in panes)
    h = f' data-hook="{esc(hook)}"' if hook else ""
    foot = f'<div class="props-foot">{foot_html}</div>' if foot_html else ""
    labels = [label for _, label, _, _ in panes]
    labels = labels[:1] + [x[:1].lower() + x[1:] for x in labels[1:]]           # one phrase: "Properties and definitions"
    named = labels[0] if len(labels) == 1 else ", ".join(labels[:-1]) + " and " + labels[-1]
    return (f'<div class="props" data-tabs{h}><div class="props-head"><nav class="props-tabs" '
            f'aria-label="{esc(named)}">{tabs}</nav><div class="props-count">{counts}</div></div>{body}{foot}</div>')


# ---------------------------------------------------------------------------
# the document layout and the page
# ---------------------------------------------------------------------------

def doc(body_html, toc_entries=(), *, wide=False):
    """A document page's body: its contents in a column beside it (stacked on phones), the text
    in a card."""
    side = f'<aside class="doc-side">{toc(toc_entries)}</aside>' if toc_entries else ""
    cls = "doc" + (" doc-wide" if wide else "")
    if not toc_entries:
        return f'<div class="card doc-body{" doc-wide" if wide else ""}">{body_html}</div>'
    return f'<div class="{cls}">{side}<article class="card doc-body">{body_html}</article></div>'


# the courses (decided 2026-11-11/12: sky130, and ASAP7 placed and routed in place of "ASAP7 · cells only"); the routed
# course has a `?pdk=` key of its own, asap7pnr, so that a copied link never changes its meaning: an old ?pdk=asap7 is
# taken as asap7pnr by pdk.js, which tells the reader so
PDK_OPTIONS = (("sky130", "sky130"), ("asap7pnr", "ASAP7 · placed and routed"))


def pdk_select(id_, label_html, *, cls="pdk-pick"):
    """The library selector, "the course" (decided 2026-11-09: a reader chooses the library the golf scores are shown
    on): a `<select>` of PDK_OPTIONS, sky130 chosen, hidden until pdk.js shows it (without JavaScript it could do
    nothing: `pdk_nojs` says so instead). `label_html` None: no label of its own.
    `autocomplete="off"`: a browser restores no earlier value of it on Back, after pdk.js has set it to the view shown."""
    opts = "".join(f'<option value="{v}"{" selected" if v == "sky130" else ""}>{esc(t)}</option>' for v, t in PDK_OPTIONS)
    label = f'<label for="{esc(id_)}">{label_html}</label>' if label_html is not None else ""
    return (f'<div class="{cls}" data-pdk-pick hidden>{label}'
            f'<select id="{esc(id_)}" data-pdk-select autocomplete="off">{opts}</select></div>')


def pdk_nojs(text_html, cls="pdk-nojs"):
    """What a reader without JavaScript sees in the selector's place: the scores are sky130's, and the routed course
    needs the selector."""
    return f'<noscript><p class="{cls}">{text_html}</p></noscript>'


def layout(*, title, body_html, root, active=None, description="", revision=None, site_name="svGolf",
           tagline="", library=None, foot_repo=(), scripts=(), banner_html="", header_pdk=True, url=None,
           base_href=None, skip_link=True, robots=None):
    """A complete page. `root` is the relative path from the page to the site
    root ("" for a top-level page, "../../" for tasks/<t>/index.html). `scripts`: the site's own
    script files the page loads after site.js (a task page: charts.js). The header carries the library
    selector, "Course" (`pdk_select`; pdk.js, loaded first and not deferred, sets <html data-pdk> before the page is
    drawn), unless `header_pdk` is false (the 404 page, which shows no scores; since 2026-11-13 the front page has the
    header's selector too, one control in one place on every page); `banner_html` (a page that shows scores: the old link's notice, build.py `moved_note`) opens the main
    column. `tagline`: the footer's line beside the name (the front page's headline). The footer's links, one row (decided 2026-11-11): the
    licence, then `foot_repo` ([(label, url)]: the public repository's Source, Issues and Contributing; empty
    without one), `library` ({name, url}: the Lean library the proofs are written with), the roadmap, how to
    reproduce a score, llms.txt, the data and the revision; since 2026-11-13 also "How it is scored" (the rules
    page's "The courses", which holds what the routed course's banner and the front page's course lines said).
    `foot_repo` may hold ("Apache-2.0", url) first: the licence's link. A `title` that starts with the site's name ("svGolf: ...", the front page's) is the whole title;
    any other gets " | svGolf". The link preview: the page's `url` (its published address, absolute) is its canonical
    address and og:url; og:title and og:description repeat the title and the description; no image (decided
    2026-11-12). `base_href` (the 404 page, which the host serves at any depth): every relative address resolves from
    the site's root; `skip_link` false leaves out the skip link (an in-page `#main` would resolve to the root under a
    base); `robots`: the robots meta tag's value."""
    current = ' aria-current="page"'
    logo = pixelart.logo()          # the mark: the hero's chip, small (aria-hidden)
    extra = "".join(f'\n<script src="{root}{esc(s)}" defer></script>' for s in scripts)
    nav = "".join(f'<a href="{root}{href}"{current if href == active else ""}>{esc(label)}</a>'
                  for href, label in NAV)
    rev = f"<li>revision {code(revision)}</li>" if revision else ""
    repo = dict(foot_repo)
    licence = (f'<li><a href="{esc(repo["Apache-2.0"])}">Apache-2.0</a></li>' if "Apache-2.0" in repo
               else "<li>Apache-2.0</li>")
    links = (licence
             + "".join(f'<li><a href="{esc(url)}">{esc(label)}</a></li>' for label, url in foot_repo
                       if label != "Apache-2.0")
             + (f'<li>Lean library: <a href="{esc(library["url"])}">{esc(library["name"])}</a></li>' if library else "")
             + f'<li><a href="{root}rules.html#courses">How it is scored</a></li>'          # build.py COURSES_ANCHOR
             + f'<li><a href="{root}roadmap.html">Roadmap</a></li>'
             + f'<li><a href="{root}reproduce.html">Reproduce a score</a></li>'
             + f'<li><a href="{root}llms.txt">llms.txt</a></li><li><a href="{root}data/site.json">data</a></li>' + rev)
    full_title = title if title == site_name or title.startswith(f"{site_name}: ") else f"{title} | {site_name}"
    pick = (pdk_select("pdk-select", "Course") + pdk_nojs("Course: sky130 · the routed ASAP7 course needs JavaScript")
            if header_pdk else "")
    base = f'\n<base href="{esc(base_href)}">' if base_href else ""
    meta = (f'\n<meta name="robots" content="{esc(robots)}">' if robots else "")
    meta += f'\n<link rel="canonical" href="{esc(url)}">' if url else ""
    meta += (f'\n<meta property="og:type" content="website">\n<meta property="og:site_name" content="{esc(site_name)}">'
             f'\n<meta property="og:title" content="{esc(full_title)}">')
    meta += f'\n<meta property="og:description" content="{esc(description)}">' if description else ""
    meta += f'\n<meta property="og:url" content="{esc(url)}">' if url else ""
    meta += '\n<meta name="twitter:card" content="summary">'
    skip = '<a class="skip" href="#main">Skip to the content</a>\n' if skip_link else ""
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">{base}
<title>{esc(full_title)}</title>
<meta name="description" content="{esc(description)}">{meta}
<link rel="icon" href="{root}favicon.svg" type="image/svg+xml">
<link rel="icon" href="{root}favicon-32.png" type="image/png" sizes="32x32">
<link rel="stylesheet" href="{root}style.css">
<script src="{root}pdk.js"></script>
<script src="{root}site.js" defer></script>{extra}
</head>
<body>
{skip}<header class="site-header"><div class="wrap">
<a class="brand" href="{root}index.html"><span class="brand-mark">{logo}</span>{esc(site_name)}</a>
{pick}
<nav class="site-nav" aria-label="Site">{nav}</nav>
</div></header>
<main id="main">
{banner_html}{body_html}
</main>
<footer class="site-footer"><div class="wrap">
<div class="foot-brand"><span class="brand-mark">{logo}</span><p><strong>{esc(site_name)}</strong>{esc(tagline)}</p></div>
<ul class="foot-links">{links}</ul>
</div></footer>
</body>
</html>
"""
