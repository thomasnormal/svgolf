"""The pages of an EXPLORATION task (kind `explore-stream`: a task without a trusted statement yet).

An exploration task has no proved records, no par of a ranked board and no leaderboard. Its page shows the task
(the README's own sections), and an exploration board of UNPROVED entries (leaderboard/explore/<task>.json), every
number labelled `composed` and `unproved`, on a page of its own kind: nothing of it appears on a ranked board, in
the latest records, in the charts or in the machine-readable boards. Its pages are under explore/, not tasks/. The
home page lists it in a block of its own under the ranked tasks' cards, headed "Exploration".

build.py calls `collect` (the tasks), `home_html` (the home page's block) and `task_page` (the page and the files
it offers). The texts come from the task's README.md; site/content/tasks/<t>.json gives the display title and
subtitle, and which README sections the page shows open (`sections`) or folded (`folded`).

A player's entry (2026-11-26; leaderboard/exploreboard.py, "A PLAYER'S ENTRY") shows its player on the board, and
its writeup on a page of its own, explore/<t>/entries/<name>.html, with the entry's numbers and who helped: the
writeup rendered as a record's is (site/writeup.py, through site/safehtml.py's allowlists), the page of the
exploration kind (unproved, composed).
"""
import html
import json
import os
import posixpath

import md
import page
import writeup

esc = html.escape
code = page.code


class ExploreTask:
    def __init__(self, name, task, info, board):
        self.name, self.task, self.info, self.board = name, task, info, board
        self.dir = f"svgolf/tasks/{name}"
        self.page = f"explore/{name}/index.html"       # (not under tasks/: those are the ranked tasks' pages)
        self.title = info.get("title") or task.get("title", name)
        self.subtitle = info.get("subtitle", "")
        self.number = None


def collect(site, lbx, names, tasks_dir, listing, build_error):
    """The exploration tasks config.json `explore_tasks` lists (`listed`), in its order."""
    out = []
    for name in names:
        how = listing.get(name)
        if how is None:
            site.warn(f"exploration task {name} is not in config.json `explore_tasks`: hidden")
            continue
        if how == "hidden":
            continue
        if how != "listed":
            raise build_error(f"config.json `explore_tasks`: {name}: the listing is `listed` or `hidden`, not {how!r}")
        with open(os.path.join(tasks_dir, name, "task.json"), encoding="utf-8") as fh:
            task = json.load(fh)
        info = site.content(f"tasks/{name}.json")
        if info is None:
            raise build_error(f"{name}: an exploration task needs site/content/tasks/{name}.json (title, subtitle, "
                              "sections)")
        bad = lbx.problems(name)
        if bad:
            raise build_error("exploration board: " + "; ".join(bad))
        out.append(ExploreTask(name, task, info, lbx.load(name)))
    return out


def fmt_area(um2):
    return f"{um2 / 1e6:.3f}"


def fmt_int(n):
    return f"{n:,}".replace(",", " ")


def score_text(lbx, e):
    return f"{lbx.mm2ms(e):.2f}"


def best(lbx, t):
    rows = lbx.ordered(t.board)
    return rows[0] if rows else None


def status_badge():
    return page.badge("exploration: unproved entries", "draft")


def home_html(lbx, tasks, here, rel_link):
    """The home page's block of exploration tasks, under the ranked tasks' cards and apart from them: a heading of
    its own, one sentence, the cards."""
    if not tasks:
        return ""
    cards = "".join(card_html(lbx, t, here, rel_link) for t in tasks)
    return ('<section class="course"><div class="section-head" id="exploration"><h2>Exploration</h2></div>'
            '<p class="small muted">No statement yet, so nothing here is proved: the entries are unproved designs, '
            'checked by simulation, and their scores are composed.</p>'
            f'<ul class="task-cards explore-cards">{cards}</ul></section>')


def card_html(lbx, t, here, rel_link):
    """An exploration task's card: its label says exploration, and its numbers are the plain design's and the best
    entry's composed scores, under names of their own."""
    number = numbers_html(lbx, t)
    return (f'<li class="task-card explore-card"><div class="task-card-top"><span class="task-no">'
            f'<span class="label label-accent task-start">explore</span></span>'
            f'<span class="label">exploration · {code(t.name)}</span></div>'
            f'<h3>{page.link(rel_link(here, t.page), esc(t.title))}</h3>'
            + (f"<p>{esc(t.subtitle)}</p>" if t.subtitle else "")
            + f'<div class="tags">{status_badge()}</div>{number}</li>')


def numbers_html(lbx, t):
    """The task's numbers, in the ranked tasks' place but under other names: the plain design and the best entry
    (composed scores, never "par" and "record" of a ranked board), and how many entries there are, all unproved."""
    b, p = best(lbx, t), lbx.par_entry(t.board)
    if not b or not p:
        return ""
    n = len(t.board["entries"])
    return page.stats([
        page.Stat("Plain design", score_text(lbx, p), unit="mm²·ms", title="The plain classical array's composed "
                  "score, unproved: area × cycles per job × period"),
        page.Stat("Best entry", score_text(lbx, b), unit="mm²·ms", title="The best composed score among the "
                  "unproved entries"),
        page.Stat("Unproved", f"{n} {'entry' if n == 1 else 'entries'}", title="No entry of this task has a proof")])


def entry_page_path(t, e):
    return f"explore/{t.name}/entries/{e['name']}.html"


def board_html(lbx, t, here, rel_link, writeups=()):
    """The exploration board: the entries by composed score, par marked, every row unproved; a player's entry with
    its player, its title linking its page (`writeups`: the names of the entries that have one)."""
    rows = lbx.ordered(t.board)
    if not rows:
        return "<p>No entry yet.</p>"
    par = lbx.par_entry(t.board)
    body = []
    for e in rows:
        s = e["score"]
        rel = f"{lbx.score_value(e) / lbx.score_value(par):.3f}" if par else ""
        name = (page.link(rel_link(here, f"explore/{t.name}/entries/{e['name']}.sv"), code(e["name"]))
                + (" " + page.badge("par", "par") if e.get("par") else ""))
        title = esc(e["title"])
        if e["name"] in writeups:
            title = page.link(rel_link(here, entry_page_path(t, e)), title)
        by = f" · by {esc(e['player'])}" if "player" in e else ""
        body.append([f'{name}<br><span class="small muted">{title}{by}</span>',
                     f"<strong>{score_text(lbx, e)}</strong>", rel, fmt_area(s["area_um2"]), fmt_int(s["cycles"]),
                     fmt_int(s["period_ps"])])
    table = page.table(["entry", "score, mm²·ms per job", "× par", "area, mm²", "cycles per job", "period, ps"], body,
                       numeric=(1, 2, 3, 4, 5), stack=True)
    return table


def entry_page(site, lbx, t, e, w, rel_link):
    """explore/<t>/entries/<name>.html, a player's entry: the writeup `w` (title, body HTML, source path) as a
    record page's writeup card, beside the entry's player, who helped, its note and its composed numbers."""
    here = entry_page_path(t, e)
    title, body_html, src = w
    s, par = e["score"], lbx.par_entry(t.board)
    rel = f"{lbx.score_value(e) / lbx.score_value(par):.3f}" if par else ""
    head = page.page_head(
        crumbs_html=(f'<a href="{rel_link(here, "index.html")}"><span class="back" aria-hidden="true">‹</span>'
                     f'Tasks</a> / {page.link(rel_link(here, t.page), esc(t.name))} / {esc(e["name"])}'),
        title_html=f'{esc(title)} <span class="task-id">{code(e["name"])}</span>',
        sub_html=esc(e["title"]),
        tags_html=" ".join([status_badge(), page.badge("ASAP7 · composed score", "plain")]),
        aside_html=page.stats([
            page.Stat("Score", score_text(lbx, e), unit="mm²·ms", title="The entry's composed score, unproved: area × "
                      "cycles per job × period"),
            *([page.Stat("× par", rel, title="The score over the plain classical array's")] if par else [])]))
    pairs = [("entry", f'{code(e["name"])} on the {page.link(rel_link(here, t.page) + "#board", "exploration board")}'),
             ("player", esc(e["player"])),
             ("assisted by", esc("; ".join(e.get("assisted_by") or [])) or '<span class="muted">none</span>'),
             ("note", esc(e.get("note") or "")),
             ("area", f"{fmt_area(s['area_um2'])} mm², of which on-chip memory {fmt_area(s['sram_area_um2'])} mm²"),
             ("cycles per job", f"{fmt_int(s['cycles'])}, measured on the scored job"),
             ("period", f"{fmt_int(s['period_ps'])} ps, the slowest module's ({code(s['slowest_module'])})"),
             ("proof", "none: the entry is unproved")]
    files = '<div class="btn-row">' + "".join(
        page.button(rel_link(here, f"explore/{t.name}/entries/{e['name']}{ext}"), esc(f"{e['name']}{ext}"),
                    "quiet sm", download=True) for ext in (".sv", ".json")) + "</div>"
    entry = page.card(page.dl(pairs) + files, id_="entry", label_html="This entry")
    wcard = page.card(f'<div class="writeup-body">{body_html}</div>', tag="section", id_="writeup",
                      title_html="The writeup", cls="writeup",
                      foot_html=f'<p class="fine">From {code(page.shown_path(src))}, kept beside the board.</p>')
    site.page(here, f"{title} ({t.name}: {e['name']})",
              head + f'<div class="split"><div class="col">{wcard}</div><div class="col">{entry}</div></div>',
              description=f"svGolf exploration task {t.name}, the entry {e['name']} by {e['player']}: {e['title']}. "
                          "Unproved; composed score.")


def facts_html(t):
    task = t.task
    sp, job = task["scoring"]["params"], task["scoring"]["job"]
    pts = ", ".join("(" + ", ".join(f"{k} = {v}" for k, v in sorted(p["params"].items())) + ")"
                    for p in task["explore"]["points"])
    pairs = [("top module", code(task["top"])),
             ("parameters", ", ".join(f"{code(p['name'])} in range {code(p['range'])}" for p in task["parameters"])),
             ("scored job", f"N = {1 << job['lgn']}, batch {job['batch']}, at "
              + ", ".join(f"{code(k)} = {v}" for k, v in sorted(sp.items()))),
             ("score", "area × cycles × period on the ASAP7 cells-only view, composed module by module; lower is "
              "better"),
             ("simulated at", pts + "; the scored job itself, with identity weights"),
             ("proof", "none yet: every entry is unproved")]
    return page.dl([(esc(k), v) for k, v in pairs])


def task_page(site, lbx, t, rel_link, read_text, build_error):
    """tasks/<t>/index.html and the files it offers."""
    here = t.page
    readme = f"{t.dir}/README.md"
    # the files the page offers, byte for byte; README links to them resolve to these copies
    offered = []
    for rel in t.info.get("files", []):
        src = f"{t.dir}/{rel}" if not rel.startswith("svgolf/") else rel
        dest = f"explore/{t.name}/{rel}" if not rel.startswith("svgolf/") else f"explore/{t.name}/{rel[len('svgolf/'):]}"
        site.copy(dest, src)
        site.task_pages[src] = dest
        offered.append((rel, dest))
    writeups = {}
    for e in t.board["entries"]:
        for key, ext in (("sv", ".sv"), ("declare", ".json")):
            dest = f"explore/{t.name}/entries/{e['name']}{ext}"
            site.copy(dest, "svgolf/" + e[key])
            site.task_pages.setdefault("svgolf/" + e[key], dest)
        if "player" in e:
            # what the player wrote stays exempt from the internal markers, as a record's fields are
            site.player_text.update([e["player"], *e.get("assisted_by", []), e.get("note") or ""])
            path = lbx.writeup_path(t.name, e["name"])
            src = "svgolf/" + os.path.relpath(path, lbx.SVGOLF).replace(os.sep, "/")
            try:
                w_title, w_body = writeup.render(read_text(src), source=src)
            except ValueError as err:          # (collect's `problems` refuses a missing or malformed one first)
                raise build_error(f"{src}: {err}") from None
            writeups[e["name"]] = (w_title, w_body, src)
            entry_page(site, lbx, t, e, writeups[e["name"]], rel_link)
    site.task_pages[readme] = here
    text = read_text(readme)
    lines = text.split("\n")
    secs = {title: (start, end) for level, title, start, end in md.split_sections(text) if level in (2, 3)}
    slugger = md.Slugger(["board", "facts", "files", "task"])

    def section(title, shift=1):
        if title not in secs:
            raise build_error(f"{readme}: no section {title!r} (site/content/tasks/{t.name}.json names it)")
        s0, s1 = secs[title]
        return site.render_md("\n".join(lines[s0 + 1:s1]), source=readme, here=here, first_line=s0 + 2,
                              slugger=slugger, heading_shift=shift).html

    def lead():
        first = min(start for start, _ in secs.values())
        body = "\n".join(lines[1:first])
        cut = body.find("\n| file |")
        return site.render_md(body[:cut] if cut >= 0 else body, source=readme, here=here, first_line=2,
                              slugger=slugger).html

    head = page.page_head(
        crumbs_html=(f'<a href="{rel_link(here, "index.html")}"><span class="back" aria-hidden="true">‹</span>'
                     f"Tasks</a> / {esc(t.name)}"),
        title_html=f'{esc(t.title)} <span class="task-id">{code(t.name)}</span>',
        sub_html=esc(t.subtitle) if t.subtitle else None,
        tags_html=" ".join([status_badge(), page.badge("ASAP7 · composed score", "plain")]),
        aside_html=f'<section id="numbers">{numbers_html(lbx, t)}</section>')
    open_secs = "".join(
        f'<section id="{esc(slugger.slug(title))}"><h3>{esc(title)}</h3>{section(title)}</section>'
        for title in t.info.get("sections", []))
    folded = "".join(page.details(esc(title), section(title), id_=slugger.slug(title))
                     for title in t.info.get("folded", []))
    task_card = page.card(lead() + open_secs + folded, tag="article", id_="task", label_html="This task")
    board = page.card(
        board_html(lbx, t, here, rel_link, writeups), tag="section", id_="board",
        title_html="Exploration board", flush=True,
        actions_html='<span class="label">unproved · composed · lower is better</span>',
        foot_html=('<p class="small">Not a leaderboard: no entry here has a proof. Each passed the simulation check, '
                   f'which a wrong design can pass too ({page.link("#what-the-check-does-not-show", "what it does not show")}). '
                   "The cycles per job were measured by running the scored job with identity weights; the area and "
                   "the period are composed from the modules: no wires, no clock tree "
                   f'({page.link("#scoring", "how the score is composed")}).</p>'))
    facts = page.card(facts_html(t), id_="facts", label_html="At a glance")
    files = page.card('<div class="btn-row">'
                      + "".join(page.button(rel_link(here, dest), esc(posixpath.basename(rel)), "quiet sm",
                                            download=True) for rel, dest in offered) + "</div>",
                      id_="files", label_html="Files")
    # the board across the page, under the head (six columns do not fit beside the task); then the task and the facts
    body = (head + board + f'<div class="split"><div class="col">{task_card}</div>'
            f'<div class="col">{facts}{files}</div></div>')
    site.page(here, f"{t.title} ({t.name})", body,
              description=f"svGolf exploration task {t.name}: {t.title}. {t.subtitle} Entries are unproved.")
