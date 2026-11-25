"""The svGolf site as a whole: built once with --offline into a temporary
directory, then checked file by file against the repository.

    python3 -m unittest discover -s svgolf/tests/site      (from the lean-surfaces root)

No network, no Yosys, no Lean. The checks are written independently of the
generator's own guards (site/build.py runs a link check and the denylist
scan itself; these tests do not reuse that code).
"""

import contextlib
import glob
import hashlib
import html
import html.parser
import importlib.util
import io
import json
import os
import posixpath
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import types
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
SITE = os.path.join(SVGOLF, "site")
BUILD_PY = os.path.join(SITE, "build.py")


def load_build():
    """site/build.py under a private name (a module called `build` may be installed)."""
    sys.path.insert(0, SITE)
    spec = importlib.util.spec_from_file_location("svgolf_site_build", BUILD_PY)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


build = load_build()
lb = build.lb
sys.path.insert(0, HERE)
from pdkview import view_of  # noqa: E402  (a page as one library's reader sees it)


def read_tree(top):
    out = {}
    for d, dirs, files in os.walk(top):
        dirs.sort()
        for f in sorted(files):
            p = os.path.join(d, f)
            with open(p, "rb") as fh:
                out[os.path.relpath(p, top).replace(os.sep, "/")] = fh.read()
    return out



# the tasks whose par design waits for a routed run: every par was routed on 2026-11-13; since 2026-11-24 fdivp's is
# pending again (the new rating build changed its ASAP7 netlist; `asap7pnr --rebind`), until the course host routes it
# at its stored seed. SiteTest.test_the_routed_pars_that_wait_are_the_data_s checks this set against the data.
PNR_PAR_PENDING = {"fdivp"}

class Page(html.parser.HTMLParser):
    """The ids, links, tags and `<pre data-src>` texts of one page."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids, self.links, self.tags, self.marks = set(), [], [], []
        self.src_blocks, self._pre, self._buf = [], None, []
        self.base = None

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        self.tags.append((tag, a))
        if a.get("id"):
            self.ids.add(a["id"])
        if tag == "base":                     # where the page's relative links resolve from, not a link
            self.base = a.get("href")
            return
        for k in ("href", "src"):
            if a.get(k) is not None:
                self.links.append((tag, k, a[k]))
        if tag == "pre" and "data-src" in a:
            self._pre, self._buf = a["data-src"], []
        if tag == "g" and "data-kind" in a:
            self.marks.append(a)

    def handle_endtag(self, tag):
        if tag == "pre" and self._pre is not None:
            self.src_blocks.append((self._pre, "".join(self._buf)))
            self._pre = None

    def handle_data(self, data):
        if self._pre is not None:
            self._buf.append(data)


def parse(data):
    p = Page()
    p.feed(data.decode("utf-8"))
    p.close()
    return p


def pinned_flow(flow="comb"):
    """tests/expected.json's pin of the flow `flow` (`flow`; `flow_seq` for the clocked flow, the pin a clocked task's
    records are compared with) in leaderboard.py's form."""
    with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
        pin = json.load(fh)["flow_seq" if flow == "seq" else "flow"]
    return {"yosys": pin["yosys_version"], "canon_script_sha256": pin["canon_script_sha256"],
            "script_sha256": pin["script_sha256"], "ge_table_sha256": pin["ge_table_sha256"]}


def records():
    return lb.good_records(lb.load_records(os.path.join(SVGOLF, "leaderboard", "data")))


def shown_refs(task):
    """The task.json references the site shows (decided 2026-11-12): the proofs of par's design, the one design
    leaderboard/par.json names; every other reference is an entry, shown once a player's record holds it."""
    par = lb.par_names(os.path.join(SVGOLF, "tasks"), task)
    return [r for r in task.get("references", [])
            if lb.sha256_file(os.path.join(SVGOLF, "tasks", task["name"], r["sv"])) in par]


def waiting_refs(task):
    """The task.json references the site does not show (decided 2026-11-12): entries until they are recorded."""
    shown = [r["sv"] for r in shown_refs(task)]
    return [r for r in task.get("references", []) if r["sv"] not in shown]


def table_rows(h):
    """The rows of every table in the HTML `h`, each a list of its cells' text (whitespace runs as one space)."""
    return [[norm(text_of(c)).strip() for c in re.findall(r"<t[dh]\b[^>]*>(.*?)</t[dh]>", tr, re.S)]
            for tr in re.findall(r"<tr\b.*?</tr>", h, re.S)]


def read_text_file(rel):
    """A file of svGolf's own tree, by its path relative to svgolf/."""
    with open(os.path.join(SVGOLF, *rel.split("/")), encoding="utf-8") as fh:
        return fh.read()


def text_of(data):
    """A page's text: tags dropped, entities decoded."""
    s = data.decode("utf-8") if isinstance(data, bytes) else data
    return html.unescape(re.sub(r"<[^>]+>", "", s))


def norm(s):
    """Text compared loosely: Markdown code marks dropped, whitespace collapsed."""
    return " ".join(s.replace("`", "").split())


def sky130_scores(task_name):
    """{design file sha256: exact area x time (1e-4 um^2 x ps)} of the task's designs at its scoring
    point, read here from the sources the site must use (the sky130 goldens of score/tests/ppa/ for
    a combinational design, else a reference's own record, tests/expected.json's clocked columns),
    independently of the generator."""
    task = lb.load_task(os.path.join(SVGOLF, "tasks"), task_name)
    point = lb.scoring_point(task)
    out = {}
    with open(os.path.join(SVGOLF, "score", "tests", "ppa", "designs.json"), encoding="utf-8") as fh:
        designs = json.load(fh)["designs"]
    with open(os.path.join(SVGOLF, "score", "tests", "ppa", "expected_ppa.json"), encoding="utf-8") as fh:
        gold = json.load(fh)["designs"]
    for d in designs:
        if d["task"] == task_name and (d.get("params") or {}) == point and d["name"] in gold:
            with open(os.path.join(SVGOLF, d["src"]), "rb") as fh:
                out[hashlib.sha256(fh.read()).hexdigest()] = gold[d["name"]]["area_e4um2"] * gold[d["name"]]["delay_ps"]
    # a reference with no golden: its own record's sky130 columns, when comparable (the current pins and the task's drive)
    ident, drive = lb.ppa_identity(), lb.ppa_setup_now(task).get("input_drive")
    for r in records():
        p = r.get("ppa") or {}
        if (r["task"] == task_name and r["player"] == "svgolf-reference" and p.get("available") is True
                and r["files"]["sv"]["sha256"] not in out and r["score"]["scoring_point"] == point
                and all(p.get(k) == ident.get(k) for k in lb.PPA_IDENTITY) and lb.ppa_input_drive(p) == drive):
            out[r["files"]["sv"]["sha256"]] = p["area_e4um2_sky130"] * p["delay_ps_sky130"]
    with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
        exp = json.load(fh)["tasks"].get(task_name, {})
    key = ",".join(f"{k}={v}" for k, v in point.items()) or "default"
    for ref in task.get("references", []):
        s = ((exp.get("references", {}).get(posixpath.splitext(posixpath.basename(ref["sv"]))[0]) or {})
             .get("scores") or {}).get(key) or {}
        if "time_ps" in s:
            with open(os.path.join(SVGOLF, "tasks", task_name, ref["sv"]), "rb") as fh:
                out[hashlib.sha256(fh.read()).hexdigest()] = round(s["area_um2"] * 10000) * s["time_ps"]
    return out


def par_score(task_name):
    """The exact score of the task's par design (decided 2026-11-12: one design per task, leaderboard/par.json; it was the
    best proved reference's), or None when it is not weighed."""
    task = lb.load_task(os.path.join(SVGOLF, "tasks"), task_name)
    scores = sky130_scores(task_name)
    mine = [scores[sha] for sha in lb.par_names(os.path.join(SVGOLF, "tasks"), task) if sha in scores]
    return min(mine) if mine else None


def roadmap_part(page_html, status):
    """The items of roadmap.html under one status's heading (`<h2 id=status>` to the next heading)."""
    m = re.search(rf'<h2 id="{re.escape(status)}"', page_html.decode("utf-8") if isinstance(page_html, bytes)
                  else page_html)
    if not m:
        raise AssertionError(f"roadmap.html has no {status!r} heading")
    rest = (page_html.decode("utf-8") if isinstance(page_html, bytes) else page_html)[m.end():]
    return rest.split("<h2", 1)[0]


def section(page_html, sid):
    """The inner HTML of a page's `<section id=sid>`, or of the `<div id=sid>` when there is no such section
    (other attributes, a card's class, allowed): a pane of the statement's tabs is a div, "What does not count"
    among them since 2026-11-09. Nested elements of the same name are counted, so a section that holds a section
    (or a div that holds divs) comes back whole."""
    for tag in ("section", "div"):
        m = re.search(rf'<{tag}\b[^>]*\bid="{re.escape(sid)}"[^>]*>', page_html)
        if m:
            break
    else:
        raise AssertionError(f"no <section id={sid!r}> or <div id={sid!r}>")
    depth, at = 1, m.end()
    for t in re.finditer(rf"<(/?){tag}\b[^>]*>", page_html[at:]):
        depth += -1 if t.group(1) else 1
        if depth == 0:
            return page_html[at:at + t.start()]
    raise AssertionError(f"<{tag} id={sid!r}> is not closed")


def element_end(h, at, tag):
    """Where the element `<tag ...>` that opens at `h[at]` ends (after its closing tag), counting nested ones."""
    depth = 0
    for m in re.finditer(rf"<(/?){tag}\b[^>]*>", h[at:]):
        depth += -1 if m.group(1) else 1
        if depth == 0:
            return at + m.end()
    raise AssertionError(f"<{tag}> at {at} is not closed")


class _Blocks(html.parser.HTMLParser):
    """The paragraphs of a piece of a page (p, li, dd, td, th, figcaption, blockquote: the innermost one holds the
    text), each {"text", "links"}: its links in order, each {"href" (None for span.unlinked), "title", "cls", "after"
    (the text right after it)}."""
    BLOCKS = {"p", "li", "dd", "td", "th", "figcaption", "blockquote"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.out, self.stack, self.a, self.last = [], [], None, None

    @classmethod
    def of(cls, part):
        b = cls()
        b.feed(part)
        b.close()
        return b.out

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag in self.BLOCKS:
            self.stack.append({"text": "", "links": []})
            self.last = None
        elif self.stack and (tag == "a" or (tag == "span" and "unlinked" in (a.get("class") or "").split())):
            link = {"href": a.get("href") if tag == "a" else None, "title": a.get("title"),
                    "cls": a.get("class") or "", "text": "", "after": "", "tag": tag}
            self.stack[-1]["links"].append(link)
            self.a = link

    def handle_endtag(self, tag):
        if self.a is not None and tag == self.a["tag"]:
            self.last, self.a = self.a, None
        elif tag in self.BLOCKS and self.stack:
            self.out.append(self.stack.pop())
            self.last = None

    def handle_data(self, d):
        if self.stack:
            self.stack[-1]["text"] += d
            if self.a is not None:
                self.a["text"] += d
            elif self.last is not None:
                self.last["after"] += d


def player_words(dd_html):
    """The words of a record page's notes or assisted-by row as the player wrote them: the row's HTML without the
    links the site puts on the names (decided 2026-11-23) and without the "(on the board since <date>)" it writes after
    a link to a later record."""
    text = re.sub(r'(<a class="board-since"[^>]*>.*?</a>) \(on the board since \d{4}-\d{2}-\d{2}\)', r"\1", dd_html)
    return html.unescape(re.sub(r"<[^>]+>", "", text))


def _link_target(here, a, repo_url):
    """("site", the site path) | ("repo", the repository path as shown) | ("url", the address) of a link of `here`."""
    if a["href"] is None:
        return ("repo", a["title"])
    href = a["href"]
    if re.match(r"[a-z][a-z0-9+.-]*:", href):
        if repo_url:
            for shown in re.findall(r"tasks/[^/#?]+/reference/[^/#?]+", href):
                if href.split("#")[0] == build.repo_link(repo_url, "svgolf/" + shown):
                    return ("repo", shown)
        return ("url", href)
    path = href.split("#")[0]
    return ("site", posixpath.normpath(posixpath.join(posixpath.dirname(here), path)) if path else here)


def _names_in(text, rec, recs, refs, players, ref_player):
    """What a paragraph of `rec`'s page names that is not `rec` itself: ("design", stem), ("record-file", stem),
    ("hash", record_hash), ("player", handle), ("par", task)."""
    own_sha, own_stem = rec["files"]["sv"]["sha256"], rec["files"]["sv"]["name"][:-3]
    out = []
    for stem, (_, sha) in refs.items():
        if sha == own_sha or stem == own_stem:
            continue
        pat = (rf"(?<![\w.-]){re.escape(stem)}(?:\.sv|\.lean)?(?![\w-])" if "_" in stem
               else rf"(?<![\w.-]){re.escape(stem)}\.(?:sv|lean)(?![\w-])")
        if re.search(pat, text):
            out.append(("design", stem))
    for h, r in recs.items():
        stem = r["files"]["sv"]["name"][:-3]
        if (h != rec["record_hash"] and r["task"] == rec["task"] and stem not in ("solution", "solution2", "sol1")
                and stem != own_stem and stem not in refs
                and re.search(rf"(?<![\w.-]){re.escape(stem)}\.sv(?![\w-])", text)):
            out.append(("record-file", stem))
    for m in re.finditer(r"(?<![0-9a-f])[0-9a-f]{8,64}(?![0-9a-f])", text):
        hit = [h for h in recs if h.startswith(m.group(0))]
        if len(hit) == 1 and hit[0] != rec["record_hash"]:
            out.append(("hash", hit[0]))
    for p in players:
        if p != rec["player"] and re.search(rf"(?<![\w-]){re.escape(p)}(?![\w-])", text):
            out.append(("player", p))
    if rec["player"] != ref_player and re.search(
            r"(?:\bthe (?:[\w-]+ ){0,3}|^)reference\b(?! variant)|\bpar's\b|\bthe par design\b", text, re.I):
        out.append(("par", rec["task"]))
    return out


def _named_linked(name, rec, recs, refs, par, targets):
    """Whether one of the paragraph's link targets goes to what `name` names."""
    kind, v = name
    t = rec["task"]
    for k, path in targets:
        m = re.fullmatch(r"tasks/[^/]+/records/([0-9a-f]{64})\.html", path or "") if k == "site" else None
        other = recs.get(m.group(1)) if m else None
        ref = re.fullmatch(r"tasks/([^/]+)/reference/([\w-]+)\.(?:sv|lean|html)", path or "") \
            if k in ("site", "repo") else None
        if kind == "hash" and other and other["record_hash"] == v:
            return True
        if kind == "player" and other and other["player"] == v:
            return True
        if kind == "record-file" and other and other["files"]["sv"]["name"] == v + ".sv":
            return True
        if kind == "design":
            if other and other["files"]["sv"]["sha256"] == refs[v][1]:
                return True
            if ref and ref.group(1) == refs[v][0] and ref.group(2) == v:
                return True
        if kind == "par":                            # par's design, or (the Wallace reference) another reference
            shas = {sha for stem, (task, sha) in refs.items() if task == t}
            if other and other["task"] == t and other["files"]["sv"]["sha256"] in shas:
                return True
            if ref and ref.group(1) == t and ref.group(2) in refs:
                return True
    return False


class SiteTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.out = os.path.join(cls.tmp.name, "site")
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            rc = build.main(["--offline", "--out", cls.out])
        if rc != 0:
            raise AssertionError(f"build.py --offline exited {rc}")
        cls.files = read_tree(cls.out)
        cls.pages = {p: parse(d) for p, d in cls.files.items() if p.endswith(".html")}
        # what the reader of each library's view sees (the library selector; sky130 is also the page without JavaScript)
        cls.views = {pdk: {p: view_of(d.decode("utf-8"), pdk) for p, d in cls.files.items() if p.endswith(".html")}
                     for pdk in ("sky130", "asap7pnr")}
        cls.view_pages = {pdk: {p: parse(h.encode("utf-8")) for p, h in v.items()} for pdk, v in cls.views.items()}
        cls.config = build.load_config()
        cls.listed = [t for t, how in cls.config["tasks"].items() if how != "hidden"]
        cls.previews = [t for t, how in cls.config["tasks"].items() if how == "preview"]
        cls.ranked = [t for t in cls.listed if t not in cls.previews]

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def html(self, path, pdk="sky130"):
        """A page's HTML in the view of `pdk` (sky130: also what a reader without JavaScript sees)."""
        return self.views[pdk][path]

    def test_every_listed_task_has_a_page_linked_from_home(self):
        home = {v for _, k, v in self.pages["index.html"].links if k == "href"}
        for t in self.listed:
            with self.subTest(task=t):
                self.assertIn(f"tasks/{t}/index.html", self.files)
                self.assertIn(f"tasks/{t}/index.html", home)
        for t, how in self.config["tasks"].items():
            if how == "hidden":
                self.assertNotIn(f"tasks/{t}/index.html", self.files)

    def test_every_page_links_the_favicon(self):
        """Every page names the tab's mark, the SVG and the 32 px PNG, from its own relative root (2026-11-11)."""
        self.assertIn("favicon.svg", self.files)
        self.assertIn("favicon-32.png", self.files)
        for path, p in sorted(self.pages.items()):
            with self.subTest(page=path):
                root = "../" * path.count("/")
                icons = [(a.get("href"), a.get("type")) for tag, a in p.tags if tag == "link" and a.get("rel") == "icon"]
                self.assertEqual(icons, [(root + "favicon.svg", "image/svg+xml"), (root + "favicon-32.png", "image/png")])
                self.assertNotIn(b'href="data:,"', self.files[path])

    def test_link_previews_and_the_404_page(self):
        """The head's link preview (decided 2026-11-12): every page but 404.html names its published address
        (config.json `site_url`; an index.html as its directory) as its canonical address and og:url; og:title and
        og:description repeat its title and its description, which no page leaves empty; since 2026-11-17 every page,
        404.html too, names the one preview picture og.png (pixelart.preview_png, 1200 x 630) by its absolute address
        with its type, size and text, and twitter:card is the large one (before: summary, no image). 404.html, which the host serves at any depth: its links go from the site's root under a <base> (the
        path of `site_url`), it has both icon links, no in-page link (under the base one would go to the root) and is
        not indexed. sitemap.xml lists every other page; robots.txt exists only where the site is a host's root, the
        one place crawlers read it."""
        import xml.etree.ElementTree as ET
        url = self.config["site_url"]
        self.assertEqual(url, "https://thomasnormal.github.io/svgolf/")
        for path, p in sorted(self.pages.items()):
            with self.subTest(page=path):
                meta = {a.get("property") or a.get("name"): a.get("content") for tag, a in p.tags
                        if tag == "meta" and (a.get("property") or a.get("name"))}
                title = html.unescape(re.search(r"<title>(.*?)</title>", self.files[path].decode("utf-8")).group(1))
                self.assertTrue(meta["description"])
                self.assertEqual(meta["og:title"], title)
                self.assertEqual(meta["og:description"], meta["description"])
                self.assertEqual((meta["og:type"], meta["og:site_name"], meta["twitter:card"]),
                                 ("website", "svGolf", "summary_large_image"))
                self.assertEqual((meta["og:image"], meta["og:image:type"], meta["og:image:width"],
                                  meta["og:image:height"]), (url + "og.png", "image/png", "1200", "630"))
                self.assertTrue(meta["og:image:alt"].startswith("svGolf: Hardware golf, with proofs."))
                canon = [a["href"] for tag, a in p.tags if tag == "link" and a.get("rel") == "canonical"]
                if path == "404.html":
                    self.assertEqual((canon, meta.get("og:url"), p.base, meta.get("robots")),
                                     ([], None, "/svgolf/", "noindex"))
                else:
                    want = url + (path[:-len("index.html")] if path.endswith("index.html") else path)
                    self.assertEqual((canon, meta["og:url"], p.base, meta.get("robots")), ([want], want, None, None))
        nf = self.files["404.html"].decode("utf-8")
        self.assertNotIn('href="#', nf)
        self.assertIn("No page at this address.", text_of(nf))
        hrefs = [ref for tag, attr, ref in self.pages["404.html"].links if tag == "a"]
        for want in ("index.html#tasks", "rules.html", "proving.html"):
            self.assertIn(want, hrefs)
        self.assertEqual([(a.get("href"), a.get("type")) for tag, a in self.pages["404.html"].tags
                          if tag == "link" and a.get("rel") == "icon"],
                         [("favicon.svg", "image/svg+xml"), ("favicon-32.png", "image/png")])
        ns = "{http://www.sitemaps.org/schemas/sitemap/0.9}"
        locs = [e.text for e in ET.fromstring(self.files["sitemap.xml"]).iter(f"{ns}loc")]
        pages = sorted(p for p in self.files if p.endswith(".html") and p != "404.html")
        self.assertEqual(locs, [build.page_url(url, p) for p in pages])
        self.assertEqual(locs[pages.index("index.html")], url)
        self.assertNotIn("robots.txt", self.files)
        png = self.files["og.png"]
        self.assertEqual(png[:8], b"\x89PNG\r\n\x1a\n")
        self.assertEqual(struct.unpack(">II", png[16:24]), (1200, 630))

        class Stub:
            def __init__(self, cfg, files):
                self.config, self.files = cfg, dict(files)

            def add(self, path, data):
                self.files[path] = data
        root = Stub({"site_url": "https://thomasnormal.github.io/"}, {"index.html": b"", "404.html": b"", "a/b.html": b""})
        build.sitemaps(root)
        self.assertEqual(root.files["robots.txt"], "User-agent: *\nAllow: /\nSitemap: https://thomasnormal.github.io/sitemap.xml\n")
        self.assertEqual([e.text for e in ET.fromstring(root.files["sitemap.xml"]).iter(f"{ns}loc")],
                         ["https://thomasnormal.github.io/a/b.html", "https://thomasnormal.github.io/"])
        none = Stub({"site_url": None}, {"index.html": b""})
        build.sitemaps(none)
        self.assertEqual(sorted(none.files), ["index.html"])
        for bad in ("http://thomasnormal.github.io/svgolf/", "https://thomasnormal.github.io/svgolf", 7):
            with self.assertRaises(build.BuildError):
                build.site_url({"site_url": bad})

    def test_relative_links_and_anchors_resolve(self):
        bad = []
        for path, p in sorted(self.pages.items()):
            for tag, attr, ref in p.links:
                if re.match(r"^[a-z][a-z0-9+.-]*:", ref):
                    continue                      # https:, mailto: (external, and only in <a>: below)
                self.assertFalse(ref.startswith("/"), f"{path}: absolute link {ref}")
                target, _, frag = ref.partition("#")
                dest = posixpath.normpath(posixpath.join(posixpath.dirname(path), target)) if target else path
                if dest not in self.files:
                    bad.append(f"{path}: {ref} -> missing {dest}")
                elif frag and frag not in self.pages.get(dest, Page()).ids:
                    bad.append(f"{path}: {ref} -> no #{frag} in {dest}")
        self.assertEqual(bad, [])

    def test_no_inline_or_external_script_and_no_external_css(self):
        """Scripts are the site's own files (`src` a relative path, no inline code); the one inline
        `<script>` allowed is inert data (`type="application/json"`). No event handler attributes."""
        for path, p in self.pages.items():
            with self.subTest(page=path):
                for tag, a in p.tags:
                    if tag != "script":
                        continue
                    if a.get("type") == "application/json":
                        self.assertNotIn("src", a)
                        continue
                    self.assertIn("src", a, f"{path}: an inline script")
                    self.assertIsNone(re.match(r"^[a-z][a-z0-9+.-]*:", a["src"]), f"{path}: script {a['src']}")
                for body in re.findall(r"<script\b([^>]*)>(.*?)</script>", self.files[path].decode("utf-8"), re.S):
                    if 'type="application/json"' not in body[0]:
                        self.assertEqual(body[1].strip(), "", f"{path}: inline script code")
                # the page's canonical address names it and loads nothing (test_link_previews_and_the_404_page)
                canon = [a.get("href") for tag, a in p.tags if tag == "link" and a.get("rel") == "canonical"]
                self.assertLessEqual(len(canon), 1)
                for tag, attr, ref in p.links:
                    if tag != "a" and ref not in canon:   # stylesheets, scripts, images, frames: local only
                        self.assertFalse(re.match(r"^[a-z][a-z0-9+.-]*:", ref) and not ref.startswith("data:"),
                                         f"{tag} {attr}={ref}")
                for tag, a in p.tags:
                    self.assertFalse(tag in ("iframe", "object", "embed"), tag)
                    self.assertFalse(any(k.startswith("on") for k in a), f"event handler on <{tag}>")
        css = self.files["style.css"].decode("utf-8")
        self.assertNotIn("@import", css)
        self.assertIsNone(re.search(r"url\(\s*['\"]?[a-z]+:", css))

    def test_spec_and_every_data_src_block_is_the_file_verbatim(self):
        seen = set()
        for path, p in self.pages.items():
            for src, text in p.src_blocks:
                with self.subTest(page=path, src=src):
                    with open(build.repo_file(src), "rb") as fh:
                        self.assertEqual(text.encode("utf-8"), fh.read())
                    seen.add((path, src))
        for t in self.listed:
            self.assertIn((f"tasks/{t}/index.html", f"svgolf/tasks/{t}/Spec.lean"), seen)

    def test_downloads_match_the_records(self):
        recs = [r for r in records() if r["task"] in self.listed]
        self.assertTrue(recs, "the repository has records")
        for rec in recs:
            h = rec["record_hash"]
            base = f"tasks/{rec['task']}/records/{h}"
            with self.subTest(record=h[:12]):
                self.assertEqual(hashlib.sha256(self.files[base + ".sv"]).hexdigest(), rec["files"]["sv"]["sha256"])
                self.assertEqual(hashlib.sha256(self.files[base + ".lean"]).hexdigest(), rec["files"]["lean"]["sha256"])
                self.assertEqual(lb.compute_record_hash(json.loads(self.files[base + ".json"])), h)
                self.assertIn(base + ".html", self.files)

    def test_reference_and_spec_downloads_are_the_repository_files(self):
        for t in self.listed:
            task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
            pairs = [(f"tasks/{t}/Spec.lean", f"tasks/{t}/Spec.lean")]
            for ref in shown_refs(task):
                stem = posixpath.splitext(posixpath.basename(ref["sv"]))[0]
                pairs += [(f"tasks/{t}/reference/{stem}.sv", f"tasks/{t}/{ref['sv']}"),
                          (f"tasks/{t}/reference/{stem}.lean", f"tasks/{t}/{ref['lean']}")]
            for out, src in pairs:
                with self.subTest(file=out), open(os.path.join(SVGOLF, src), "rb") as fh:
                    self.assertEqual(self.files[out], fh.read())
            # (decided 2026-11-12) a reference that is not par's design is an entry: no download, no page of its own
            for ref in waiting_refs(task):
                stem = posixpath.splitext(posixpath.basename(ref["sv"]))[0]
                with self.subTest(waiting=f"{t}/{stem}"):
                    for ext in (".sv", ".lean", ".html"):
                        self.assertNotIn(f"tasks/{t}/reference/{stem}{ext}", self.files)

    def test_chart_frontier_is_the_players_board_and_pareto(self):
        """The chart's record marks are the players' records; the reference player's records are par
        (drawn as the proved references), never ranked among them."""
        recs, ref_player = records(), self.config["reference_player"]
        for t in self.listed:
            with self.subTest(task=t):
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                mine = [r for r in recs if r["task"] == t and r["player"] != ref_player]
                board = lb.build_board(task, mine, flow=pinned_flow(lb.task_flow(task)), identity=lb.ppa_identity(),
                                       input_drive=lb.ppa_setup_now(task).get("input_drive"),
                                       statement=lb.current_statement_or_none(task))
                marks = [m for m in self.view_pages["sky130"][f"tasks/{t}/index.html"].marks
                         if m["data-kind"] == "record"]
                on = {m["data-hash"] for m in marks if m["data-frontier"] == "true"}
                self.assertEqual(on, {r["record_hash"] for r in board["frontier"]})
                ranked = {r["record_hash"] for r in board["frontier"] + board["dominated"]}
                self.assertEqual(on, {r["record_hash"] for r in lb.pareto(
                    [lb.row_of(r) for r in mine if r["record_hash"] in ranked])})
                by_hash = {r["record_hash"]: r for r in mine}
                for m in marks:
                    self.assertIn(m["data-hash"], by_hash)
                    self.assertEqual(int(m["data-area-mge"]), by_hash[m["data-hash"]]["score"]["area_mge"])
                    self.assertEqual(int(m["data-depth"]), by_hash[m["data-hash"]]["score"]["depth"])

    def test_reference_records_are_par_not_players(self):
        ref_player = self.config["reference_player"]
        recs = records()
        self.assertTrue(any(r["player"] == ref_player for r in recs), "the repository has reference records")
        home = text_of(self.files["index.html"])
        self.assertNotIn(ref_player, home)
        self.assertNotIn("±0.0%", home)
        self.assertNotIn("solvers", home.lower())
        self.assertNotIn("open for submissions", home)     # the cards carry no badges (decided 2026-11-06)
        self.assertNotIn("ready to play", home)
        # no status badge: OPEN only as the Under par value of a task with no record under par (decided 2026-11-17)
        self.assertNotIn("OPEN", text_of(self.files["index.html"].decode("utf-8").replace(
            f"<dd>{build.OPEN_WORD}</dd>", "")))
        # the task page keeps its status, worded by the repository's state (2026-11-11): in the development tree no
        # public repository, so "ready to play"; in the public tree (the export sets `repo_url`, and both programs of the
        # route are there) "open for submissions", as test_submit_with_a_public_repository builds it
        said, unsaid = (("open for submissions", "ready to play") if build.submissions_open(self.config)
                        else ("ready to play", "open for submissions"))
        for t in self.ranked:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                self.assertIn(said, text_of(html_))
                self.assertNotIn(unsaid, text_of(html_))
                players = {r["player"] for r in recs if r["task"] == t and r["player"] != ref_player}
                tiles = text_of(section(html_, "numbers"))
                for big in ("Par", "Record", "Under par"):
                    self.assertIn(big, tiles)
                board = section(html_, "leaderboard")
                self.assertNotIn(ref_player, text_of(board))
                if not players and par_score(t) is not None:
                    self.assertIn("Under par0%", tiles)       # the references are the first entries
                elif not players:
                    self.assertIn("Par–", tiles)              # no sky130 weighing yet: no score
                if not players:
                    self.assertNotIn("vs par", tiles)
                    self.assertNotIn("against par", tiles)
                    self.assertIn("No submissions yet.", text_of(board))
                    self.assertNotIn("<table", board)
        for r in recs:
            if r["player"] == ref_player:
                page_ = text_of(self.files[f"tasks/{r['task']}/records/{r['record_hash']}.html"])
                # "par, not an entry" only where its proof is par's own (test_pdk, per view)
                self.assertIn("not an entry", page_)
                self.assertNotIn("on the Pareto frontier", page_)

    def test_par_is_one_design_per_task_and_every_other_design_is_an_entry(self):
        """Decided 2026-11-12: par is ONE design per task, the simplest algorithm (leaderboard/par.json); the page shows that
        design with every proof of it, the baselines with a banned operator, and the records. Every other proved
        design (a reference that is not par's design, a baseline without a banned operator) is an entry: never drawn
        as a reference or baseline line, at the scored point or any measured one, never in the task's data, until a
        player's record holds it. The rules page names each listed task's par design and its algorithm."""
        table = lb.load_par_table(os.path.join(SVGOLF, "tasks"))
        with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
            expected = json.load(fh)["tasks"]
        rules = norm(text_of(self.files["rules.html"]))
        for t in self.ranked:
            with self.subTest(task=t):
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                par = lb.par_names(os.path.join(SVGOLF, "tasks"), task)
                self.assertEqual(len(par), 1)
                data = json.loads(self.files[f"data/tasks/{t}.json"])
                self.assertEqual([r["stem"] for r in data["references"] if r["par"]], [table[t]["design"]])
                self.assertTrue(all(r["sha256"] in par for r in data["references"]), t)
                self.assertTrue(all(b["banned"] for b in data["baselines"]), t)
                waiting = ([f"reference/{posixpath.splitext(posixpath.basename(r['sv']))[0]}" for r in waiting_refs(task)]
                           + [f"baseline/{b}" for b, e in expected.get(t, {}).get("baselines", {}).items()
                              if not e.get("banned")])
                html_, page = self.page_data(t)
                ids = {d["id"] for d in page["designs"]} | {d["id"] for v in page.get("at", {}).values() for d in v}
                ids |= {ln["id"] for ln in (page.get("scaling") or {}).get("lines", [])}
                names = {n for ln in (page.get("scaling") or {}).get("lines", []) for n in ln["names"]}
                for w in waiting:
                    self.assertNotIn(w, ids)
                    self.assertNotIn(f"line/{w}", ids)
                    self.assertNotIn(w.split("/", 1)[1], names)
                    self.assertNotIn(f'id="ref-{w.split("/", 1)[1]}"', html_)
                    self.assertNotIn(f'id="baseline-{w.split("/", 1)[1]}"', html_)
                if t != "_example" and table.get(t):
                    self.assertIn(f"{t}: {table[t]['design']}, {table[t]['algorithm']}", rules)

    def test_par_is_the_par_designs_area_time(self):
        """PAR is area x time of the best weighed proved reference (computed here from the goldens),
        in the display unit; RECORD is the best of par and the players' ranked records (with no
        submissions, par). A task with no weighed reference has no score, and its score card says so
        instead of drawing."""
        c = build.combined
        recs, ref_player = records(), self.config["reference_player"]
        weighed = 0
        for t in self.ranked:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                tiles = text_of(section(html_, "numbers"))
                par = par_score(t)
                if par is None:
                    self.assertIn("No design of this task has a sky130 weighing yet", text_of(section(html_, "score")))
                    continue
                weighed += 1
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                mine = [r for r in recs if r["task"] == t and r["player"] != ref_player]
                board = lb.build_board(task, mine, flow=pinned_flow(lb.task_flow(task)), identity=lb.ppa_identity(),
                                       input_drive=lb.ppa_setup_now(task).get("input_drive"),
                                       statement=lb.current_statement_or_none(task))
                ranked = {r["record_hash"] for r in board["frontier"] + board["dominated"]}
                scores = [c.of_record(r) for r in mine if r["record_hash"] in ranked]
                best = min([par] + [s for s in scores if s is not None])
                self.assertIn("Par" + c.fmt(c.um2ns(par)) + c.UNIT, tiles)
                self.assertIn("Record" + c.fmt(c.um2ns(best)) + c.UNIT, tiles)
                data = json.loads(self.files["data/site.json"])
                summary = next(x for x in data["tasks"] if x["name"] == t)
                self.assertAlmostEqual(summary["score"]["par"], c.um2ns(par))
        self.assertGreaterEqual(weighed, 4)

    def test_previews_are_listed_and_not_ranked(self):
        """A preview (config.json `preview`) is listed on the home page and has its page, with its
        status line where a ranked task has its numbers and its leaderboard: no par, no record, no
        board, never "open for submissions"; the data says `ranked: false` and carries no board."""
        if not self.previews:                       # none since matmul and the sorter rank (2026-11-08)
            self.skipTest("config.json lists no preview")
        home_html = self.files["index.html"].decode("utf-8")
        summary = {x["name"]: x for x in json.loads(self.files["data/site.json"])["tasks"]}
        llms = self.files["llms.txt"].decode("utf-8")
        for t in self.previews:
            with self.subTest(task=t):
                with open(os.path.join(SVGOLF, "site", "content", "tasks", f"{t}.json"), encoding="utf-8") as fh:
                    note = json.load(fh)["preview_note"]
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                tiles = text_of(section(html_, "numbers"))
                self.assertIn(note, tiles)
                for big in ("Par", "Record", "Under par"):
                    self.assertNotIn(big, tiles)
                board = section(html_, "leaderboard")
                self.assertIn(note, text_of(board))
                self.assertNotIn("badge-par", board)
                self.assertNotIn("<table", board)
                self.assertNotIn("badge-par", section(html_, "references"))
                head = html_.split('<section id="numbers">', 1)[0]
                self.assertIn("preview: not ranked", head)
                self.assertNotIn("open for submissions", head)
                card = home_html.split(f'href="tasks/{t}/index.html"', 1)[1].split("</li>", 1)[0]
                self.assertIn("preview: not ranked", card)
                self.assertIn(note, text_of(card))
                self.assertNotIn("Par", text_of(card))
                s = summary[t]
                self.assertEqual((s["listing"], s["ranked"], s["par"], s["preview_note"]), ("preview", False, None, note))
                data = json.loads(self.files[f"data/tasks/{t}.json"])
                self.assertEqual((data["ranked"], data["board"], data["submissions_board"]), (False, None, None))
                self.assertFalse(any(r["par"] for r in data["references"]))
                self.assertIn(f"(`{t}`)", llms)
                self.assertIn("a preview, not ranked", llms.split(f"(`{t}`)", 1)[1].split("\n", 1)[0])
        for t in self.ranked:
            self.assertTrue(summary[t]["ranked"], t)

    def test_the_sky130_score_ranks_everywhere(self):
        """Decided 11/03: sky130 A0' ranks (area um^2, time ps); GE and depth are extra columns. The tables carry the
        sky130 pair before the GE pair, no page calls the sky130 columns unranked, and "Reproduce a score" is a page,
        generated from score/PPA.md's section of that name, linked from the rules, the home page and every task."""
        rp = self.files["reproduce.html"].decode("utf-8")
        with open(os.path.join(SVGOLF, "score", "PPA.md"), encoding="utf-8") as fh:
            ppa_md = fh.read()
        self.assertIn("## Reproduce a score", ppa_md)
        for phrase in ("Tools and pinned files", "The pinned flow, step by step", "Reproduce a recorded number",
                       "score/ppa.py --fetch-liberty", "ef34f999d582044cad9c1f4d5422504ae99702ad42baa432d75215476e5d23d5"):
            self.assertIn(phrase, ppa_md)
            self.assertIn(phrase, text_of(rp))
        self.assertNotRegex(rp, r"<h2[^>]*>The liberty")          # that section only, not the rest of PPA.md
        for src in ("rules.html", "index.html", "about.html", "roadmap.html", "llms.txt"):
            with self.subTest(page=src):
                self.assertIn("reproduce.html", self.files[src].decode("utf-8"))
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                self.assertIn("reproduce.html", section(html_, "score"))
                self.assertNotIn('id="references"', html_)              # no Par card since 2026-11-13
                for sid in ("baselines",):
                    if sid == "baselines" and 'id="baselines"' not in html_:   # a task without baselines: no card
                        continue
                    head = section(html_, sid).split("</thead>", 1)[0]
                    if "<thead" not in head:
                        continue
                    heads_ = [text_of(h) for h in re.findall(r"<th\b[^>]*>(.*?)</th>", head, re.S)]
                    self.assertLess(heads_.index("area (µm²)"), heads_.index("GE · depth"), sid)
                    self.assertIn("time (ps)", heads_, sid)
        site_text = " ".join(text_of(self.files[p]) for p in ("index.html", "roadmap.html", "about.html", "rules.html"))
        for stale in ("(unranked)", "never rank anything", "(area, depth) Pareto", "the board is unchanged"):
            self.assertNotIn(stale, site_text)
        self.assertNotIn("(area, depth) Pareto", self.files["llms.txt"].decode("utf-8"))
        summary = json.loads(self.files["data/site.json"])
        for x in summary["tasks"]:
            self.assertEqual(x["ranked_axes"], ["area_um2_sky130", "time_ps"])

    def test_the_score_is_deterministic_not_noisy(self):
        """The determinism study (2026-11-05): one build of the pinned flow gives the same numbers on every run, and
        how the circuit is written (operand order, grouping, statement order) moves them, deterministically; names
        and layout never do. No document calls that noise, offers a tie band, or says layout or statement order
        cannot move a score; the rules say it, and "Reproduce a score" names the reference build."""
        docs = ["README.md", "leaderboard/README.md", "score/PPA.md"] + [
            f"tasks/{t}/README.md" for t in sorted(os.listdir(os.path.join(SVGOLF, "tasks")))
            if os.path.isfile(os.path.join(SVGOLF, "tasks", t, "README.md"))]
        for doc in docs:
            text = " ".join(read_text_file(doc).split())
            for stale in ("mapper noise", "rewrite noise", "The noise band", "10% / 20% noise", "Proposed tie bands",
                          "not on its layout or names", "measured, not the score"):
                self.assertNotIn(stale, text, doc)
        rules = norm(text_of(self.files["rules.html"]))
        for phrase in ("The numbers are not noisy", "no tie band and no best-of-k", "Trying gate forms and orders",
                       "IEEE 1800 decides"):
            self.assertIn(phrase, rules)
        self.assertIn("The reference build", text_of(self.files["reproduce.html"]))

    def test_the_rating_build_is_on_the_rules_page_and_every_score_card(self):
        """The build ratings use (decided 2026-11-05), from score/reference_build.json: its own section of the rules
        page (in the contents too) and one line in every listed task's score card that links to it."""
        rb = json.loads(read_text_file("score/reference_build.json"))
        rules = self.files["rules.html"].decode("utf-8")
        self.assertIn(build.RATING_BUILD_ANCHOR, self.pages["rules.html"].ids)
        for w in (rb["yosys"]["sha256"], rb["abc"]["sha256"], rb["yosys"]["git_sha1"]):
            self.assertIn(w, rules)
        self.assertIn(f'href="#{build.RATING_BUILD_ANCHOR}"', rules)
        for t in self.listed:
            with self.subTest(task=t):
                page_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                self.assertIn("Rated with Yosys " + rb["yosys"]["version"], text_of(page_))
                self.assertIn(f"rules.html#{build.RATING_BUILD_ANCHOR}", page_)

    def test_the_rules_define_the_numbers_of_a_task_page(self):
        """The numbers on a task page (decided 2026-11-11, before the task page's long score caption goes): the rules
        page's own section after Scoring and before the rating build, in the contents too, with par, record and under
        par, the time of each kind of task with the listed tasks of that kind, the clock period, and how to read the
        score chart."""
        rules = self.files["rules.html"].decode("utf-8")
        for id_ in ("task-page-numbers", "par-record-under-par", "clock-period", "score-chart"):
            self.assertIn(id_, self.pages["rules.html"].ids)
        at = [rules.index(f'id="{i}"') for i in ("scoring", "the-asap7-view", build.ASAP7PNR_ANCHOR, "task-page-numbers",
                                                 "rating-build")]
        self.assertEqual(at, sorted(at))
        self.assertIn('href="#task-page-numbers"', rules.split('<article', 1)[0])          # the contents
        part = rules.split('id="task-page-numbers"', 1)[1].split('id="rating-build"', 1)[0]
        text = norm(text_of(part))
        for phrase in ("Under par is how far the record is below par, as a share of par's score",
                       "a design beats par when it is accepted with a score below par's",
                       "par while no submission beats it", "A design without a weighing on the chosen course has no score",
                       "so paths from the inputs and to the outputs count too",
                       "The clock is ideal: no clock tree and no skew", "no wires, no place and route",
                       "par's design, the first entry, dated by when it joined the task",
                       "one design per task, the simplest algorithm for it",
                       "Every other design is an entry",
                       "it is never ranked, never par and never an entry"):
            self.assertIn(phrase, text)
        # each kind's time, in the task page's words, with every listed task of that kind named in its item
        items = [norm(text_of(li)) for li in re.findall(r"<li>(.*?)</li>", part.split('id="clock-period"', 1)[1]
                                                        .split("<h3", 1)[0], re.S)]
        for t in self.listed:
            if self.config["tasks"][t] == "tutorial":
                continue
            with self.subTest(task=t):
                words = build.time_words(types.SimpleNamespace(task=lb.load_task(os.path.join(SVGOLF, "tasks"), t)),
                                         " in ns")
                mine = [i for i in items if words in i]
                self.assertEqual(len(mine), 1, words)
                names = re.match(r"a [^(]+\(([^)]*)\): ", mine[0]).group(1).split(", ")
                self.assertIn(t, names)

    def test_score_chart_and_explorer(self):
        """The score chart draws par's design (dated) and the players' records, par as a
        line, and every weighed baseline as a level marked as a banned operator, on a linear and a
        log axis, and never "not proved" (decided 2026-11-12: every baseline is proved, and a baseline shown has a banned
        operator: one without is an entry, like every reference but par's design).
        The explorer's data names every scored design with the pinned flow's numbers."""
        with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
            expected = json.load(fh)["tasks"]
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.html(f"tasks/{t}/index.html")
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                key = ",".join(f"{k}={v}" for k, v in lb.scoring_point(task).items()) or "default"
                m = re.search(r'<script type="application/json" id="task-data">(.*?)</script>', html_, re.S)
                data = json.loads(m.group(1))
                exp = expected.get(t, {})
                for d in data["designs"]:
                    if d["kind"] in ("reference", "baseline"):
                        s = exp[d["kind"] + "s"][d["name"]]["scores"][key]
                        self.assertEqual(round(d["m"]["area_ge"] * 1000), s["area_mge"], d["name"])
                        self.assertEqual(d["m"]["depth"], s["depth"], d["name"])
                refs = {posixpath.splitext(posixpath.basename(r["sv"]))[0] for r in shown_refs(task)
                        if (exp.get("references", {}).get(posixpath.splitext(posixpath.basename(r["sv"]))[0], {})
                            .get("scores") or {}).get(key)}
                self.assertEqual({d["name"] for d in data["designs"] if d["kind"] == "reference"}, refs)
                self.assertEqual(sum(1 for d in data["designs"] if d["par"]), 1 if refs and t in self.ranked else 0)
                score = section(html_, "score")
                if par_score(t) is None or t in self.previews:              # a preview draws no history
                    self.assertNotIn("<svg", score)
                    continue
                self.assertEqual(score.count('data-scale="linear"'), 2)          # wide and compact
                self.assertEqual(score.count('data-scale="log"'), 2)
                self.assertEqual(len(re.findall(r'data-scale="linear"[^>]*\bhidden\b', score)), 2)   # opens on log (2026-11-24)
                self.assertEqual(len(re.findall(r'data-scale="log"[^>]*\bhidden\b', score)), 0)
                wide = score.split('data-size="wide"', 1)[1].split("</svg>", 1)[0]
                self.assertIn('class="par-line"', wide)
                kinds = set(re.findall(r'<g class="mark[^"]*" data-kind="([a-z]+)"', wide))
                self.assertLessEqual(kinds, {"reference", "record"})
                weighed = [d for d in data["designs"] if d["kind"] == "baseline" and "adp" in d["m"]]
                self.assertEqual(wide.count('<line class="level"'), len(weighed))
                for d in weighed:
                    self.assertIn(f">{html.escape(d['name'])}</text>", wide)
                self.assertEqual(wide.count(" · baseline</text>") + wide.count(" · banned op</text>"), len(weighed))
                self.assertNotIn("not proved", score)
                self.assertTrue(all(d["banned"] for d in data["designs"] if d["kind"] == "baseline"), t)

    def test_the_routed_pars_that_wait_are_the_data_s(self):
        """PNR_PAR_PENDING (the routed-view tests skip those tasks' par) is exactly the set of listed tasks whose par
        design's routed entry is pending: when the run is made, this fails and the exception goes."""
        got = set()
        for t in self.ranked:
            task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
            stem = lb.par_stem(os.path.join(SVGOLF, "tasks"), task)
            ref = next((r for r in task.get("references") or [] if os.path.basename(r["sv"])[:-3] == stem), None)
            if ref is None:
                continue
            sha = hashlib.sha256(open(os.path.join(SVGOLF, "tasks", t, ref["sv"]), "rb").read()).hexdigest()
            entry = lb.asap7pnr_entry(lb.load_asap7pnr(t), sha)
            if entry is not None and entry.get("status") == "pending":
                got.add(t)
        self.assertEqual(got, PNR_PAR_PENDING)

    def test_every_reference_shows_when_it_joined(self):
        """The score chart plots par's design at the date it joined the task (content/reference_dates.json); since the
        Par card went (decided 2026-11-13, the owner's UI feedback item 7) the leaderboard's par row says that date as
        text, "joined YYYY-MM-DD", the same in both views."""
        dates = json.loads(read_text_file("site/content/reference_dates.json"))
        seen = 0
        for t in self.ranked:
            task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
            stem = lb.par_stem(os.path.join(SVGOLF, "tasks"), task)
            if stem not in dates.get(t, {}):
                continue
            for pdk in ("sky130", "asap7pnr"):
                if pdk == "asap7pnr" and t in PNR_PAR_PENDING:
                    continue                            # par has no routed row yet (PNR_PAR_PENDING)
                with self.subTest(task=t, view=pdk):
                    board = section(self.html(f"tasks/{t}/index.html", pdk), "leaderboard")
                    row = re.findall(r'<li class="par">(.*?)</li>', board, re.S)
                    self.assertEqual(len(row), 1)
                    self.assertIn(f"<code>{stem}</code>", row[0])
                    self.assertIn(f"joined {dates[t][stem][:10]}", norm(text_of(row[0])))
                    seen += 1
        self.assertGreaterEqual(seen, 10)

    def test_the_score_card_says_little_under_the_plot(self):
        """Decided 2026-11-11: under the plot, the Score card shows the legend, one line of links (on sky130 the rating
        build and how the score is measured; on the routed course, since 2026-11-12, what that course is and how it is
        scored, never the rating build, which does not make its numbers; Reproduce a score) and a closed note, "What the
        score, Par, Record and Under par mean", that defines them and links the rules page's "The numbers on a task
        page"; no long caption and no table "every entry by date"."""
        for t in self.listed:
            raw = self.files[f"tasks/{t}/index.html"].decode("utf-8")
            self.assertNotIn("<figcaption", section(raw, "score"))
            self.assertNotIn("every entry by date", text_of(raw))
            for pdk, note_id in (("sky130", "score-terms"), ("asap7pnr", "score-terms-asap7pnr")):
                with self.subTest(task=t, view=pdk):
                    score = section(self.html(f"tasks/{t}/index.html", pdk), "score")
                    notes = re.findall(r'<details class="note" id="([^"]+)"><summary>(.*?)</summary>(.*?)</details>',
                                       score, re.S)
                    self.assertEqual([(i, s) for i, s, _ in notes],
                                     [(note_id, "What the score, Par, Record and Under par mean")])
                    for anchor in ("par-record-under-par", "clock-period", "score-chart"):
                        self.assertIn(f'../../rules.html#{anchor}"', notes[0][2])
                    line = re.findall(r'<p class="small score-links">(.*?)</p>', score, re.S)
                    self.assertEqual(len(line), 1)
                    text = norm(text_of(line[0]))
                    self.assertIn("Reproduce a score", text)
                    self.assertIn('href="../../reproduce.html"', line[0])
                    if pdk == "asap7pnr":
                        self.assertTrue(text.startswith("ASAP7 placed and routed: wires included, one run per design · "),
                                        text)
                        self.assertIn(f'href="../../rules.html#{build.ASAP7PNR_ANCHOR}">How the routed course is '
                                      'scored</a>', line[0])
                        self.assertNotIn("Rated with", text)
                        self.assertNotIn(f'rules.html#{build.RATING_BUILD_ANCHOR}"', line[0])
                    else:
                        self.assertIn("Rated with Yosys ", text)
                        self.assertIn(f'href="../../rules.html#{build.RATING_BUILD_ANCHOR}"', line[0])
                        self.assertIn('href="../../rules.html#scoring">How the score is measured</a>', line[0])
                    if "data-score-chart>" not in score:                  # a card without a chart (a preview)
                        continue
                    # what a reader sees under the plot, the note closed: the legend, the line and How to submit's link
                    # (a phone's list of the baselines drawn as levels is the chart's own labels, moved under it)
                    under = score.split("data-score-chart>", 1)[1]
                    under = re.sub(r"<svg\b.*?</svg>|<details\b.*?</details>|<ul class=\"levels-list[^\"]*\".*?</ul>",
                                   "", under, flags=re.S)
                    self.assertLessEqual(len(norm(text_of(under)).split()), 40, norm(text_of(under)))
                    desc = re.findall(r"<desc>(.*?)</desc>", score.split("data-score-chart>", 1)[1], re.S)
                    self.assertTrue(desc)
                    # the tables it names are the page's: Baselines only where the task has that card (2026-11-11);
                    # no Par card since 2026-11-13: the leaderboard's par row says when par joined
                    tail = ("The same entries as numbers: the Leaderboard (the records with their dates, and par with "
                            "the date it joined the task) and Baselines."
                            if json.loads(self.files[f"data/tasks/{t}.json"])["baselines"] else
                            "The same entries as numbers: the Leaderboard (the records with their dates, and par with "
                            "the date it joined the task).")
                    self.assertEqual('id="baselines"' in raw, tail.endswith("Baselines."))
                    for d in desc:
                        self.assertTrue(html.unescape(d).endswith(tail), d)

    def test_the_head_labels_open_the_score_note(self):
        """The page head's Par, Record and Under par (2026-11-11): each label is a plain link to the score card's closed
        note that defines it (no hover, no title), in each view that view's copy of the note, Par and Record naming
        the routed course in its view; Under par without a minus sign. The link names the note's paragraph, so that the browser
        opens the note without JavaScript too (it does for a fragment inside a closed <details>, not for the <details>
        itself: measured in Chrome, 2026-11-11); site.js opens it either way. The front page's cards, links as a
        whole, keep plain labels."""
        for t in self.ranked:
            for pdk, note_id, text_id, labels in (
                    ("sky130", "score-terms", "score-terms-text", ["Par", "Record", "Under par"]),
                    ("asap7pnr", "score-terms-asap7pnr", "score-terms-text-asap7pnr",
                     ["Par · ASAP7 routed", "Record · ASAP7 routed", "Under par"])):
                with self.subTest(task=t, view=pdk):
                    view = self.html(f"tasks/{t}/index.html", pdk)
                    head = section(view, "numbers")
                    self.assertEqual(re.findall(r"<dt>(.*?)</dt>", head),
                                     [f'<a href="#{text_id}">{html.escape(x)}</a>' for x in labels])
                    self.assertRegex(section(view, "score"), f'<details class="note" id="{note_id}"><summary>[^<]*'
                                                             f'</summary>\\s*<p id="{text_id}">')
                    self.assertNotIn("title=", head)
                    self.assertNotRegex(text_of(head), r"Under par\s*[−-]")
        for pdk in ("sky130", "asap7pnr"):
            cards = self.html("index.html", pdk)
            self.assertNotIn("score-terms", cards)
            self.assertNotIn("· ASAP7</dt>", cards)
            self.assertNotIn("· ASAP7 routed</dt>", cards)

    def test_charts_read_without_javascript(self):
        """The server draws every chart: the explorer's controls and the score chart's switch are
        hidden until charts.js shows them, the linear drawing is shown, and charts.js is a file of
        the site loaded by the task pages and the detail pages (a record's, a reference's) only."""
        self.assertIn("charts.js", self.files)
        detail = re.compile(r"tasks/[^/]+/(index|records/[0-9a-f]{64}|reference/[A-Za-z0-9_]+)\.html")
        for path, p in self.pages.items():
            srcs = [a.get("src", "") for tag, a in p.tags if tag == "script" and a.get("src")]
            uses = any(s.endswith("charts.js") for s in srcs)
            self.assertEqual(uses, bool(detail.fullmatch(path)), path)
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                self.assertRegex(html_, r'<div class="explorer-controls" data-explorer-controls hidden>')
                self.assertIn("<svg", section(html_, "explore"))
                self.assertNotRegex(html_, r'data-scale="log"[^>]*\bhidden\b')
                if "data-scale-toggle" in html_:
                    self.assertRegex(html_, r'data-scale-toggle hidden')

    # ---- measured at several points (score/measured/<task>.json, score/points.py)

    @staticmethod
    def measured(t):
        """score/measured/<t>.json as the page shows it (decided 2026-11-12): par's design (each proof of it), the
        baselines with a banned operator and the records; every other measured design is an entry, shown once a
        player's record holds it, never as a reference or baseline line."""
        path = os.path.join(SVGOLF, "score", "measured", f"{t}.json")
        if not os.path.isfile(path):
            return None
        with open(path, encoding="utf-8") as fh:
            data = json.load(fh)
        task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
        refs = {posixpath.splitext(posixpath.basename(r["sv"]))[0] for r in shown_refs(task)}
        with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
            base = json.load(fh)["tasks"].get(t, {}).get("baselines", {})
        keep = [e for e in data["designs"] if (e["kind"] == "reference" and e["name"] in refs)
                or (e["kind"] == "baseline" and (base.get(e["name"]) or {}).get("banned") is True)
                or e["kind"] == "record"]
        return dict(data, designs=keep)

    def page_data(self, t):
        html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
        m = re.search(r'<script type="application/json" id="task-data">(.*?)</script>', html_, re.S)
        return html_, json.loads(m.group(1))

    def several(self):
        out = [t for t in self.listed if self.measured(t) and len(self.measured(t)["points"]) > 1]
        self.assertGreaterEqual(len(out), 4, out)        # add, mul, clmul, fdivp
        return out

    @staticmethod
    def sizes_file(t):
        """leaderboard/sizes/<t>.json (`leaderboard.py sizes --write`), or None."""
        path = os.path.join(SVGOLF, "leaderboard", "sizes", f"{t}.json")
        if not os.path.isfile(path):
            return None
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)

    def size_keys(self, t):
        """The sizes the explorer offers, read here from the two data files: the sizes file's, then score/measured's
        points it lacks."""
        keys = [x["key"] for x in (self.sizes_file(t) or {}).get("sizes", [])]
        keys += [p["key"] for p in (self.measured(t) or {}).get("points", []) if p["key"] not in keys]
        return keys

    def test_the_explorer_offers_every_measured_point(self):
        """A task measured at several sizes (2026-11-13: the sizes file's, leaderboard/sizes/, then score/measured/'s):
        the page data names them in the sizes file's order, the scoring one (task.json's scoring point) marked; the Size
        selector lists the same keys, the scoring one chosen and labelled "· scored", no other; every other size's
        designs measured only in score/measured/ carry its numbers, read here from that file independently of the
        generator (area in 1e-4 um^2, time, area x time, GE, depth), each marked measured. The scoring size's designs
        stay the ranked ones. A task of one size (aes_sbox) has no selector and no scaling view."""
        for t in self.listed:
            with self.subTest(task=t):
                html_, data = self.page_data(t)
                m = self.measured(t)
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                key = ",".join(f"{k}={v}" for k, v in lb.scoring_point(task).items()) or "default"
                keys = self.size_keys(t)
                if len(keys) < 2:
                    self.assertNotIn("points", data)
                    self.assertNotIn("data-size-select", html_)
                    self.assertNotIn('id="scaling"', html_)
                    continue
                self.assertEqual([p["key"] for p in data["points"]], keys)
                self.assertEqual([p["key"] for p in data["points"] if p["scored"]], [key])
                ex = section(html_, "explore")
                sky = ex.split('<div class="pdk pdk-asap7pnr">', 1)[0]
                self.assertIn('<div class="explorer-controls" data-explorer-controls hidden>'
                              '<div class="axis-control size-control"><label class="label" for="explore-size">Size</label>'
                              '<select id="explore-size" data-size-select>', sky)
                opts = re.findall(r'<option value="([^"]+)"( selected)?[^>]*>([^<]*)</option>',
                                  sky.split("data-size-select>", 1)[1].split("</select>", 1)[0])
                self.assertEqual([html.unescape(o[0]) for o in opts], keys)
                self.assertEqual([(html.unescape(o[0]), o[2].endswith("· scored")) for o in opts if o[1]], [(key, True)])
                self.assertEqual(sum(o[2].endswith("· scored") for o in opts), 1)
                self.assertEqual(data.get("preview", False), t in self.previews)
                self.assertFalse(any(d.get("measured") for d in data["designs"]))
                self.assertNotIn(key, data["at"])
                sized = {e["sv_sha256"] for e in (self.sizes_file(t) or {}).get("designs", [])}
                shas = {d["id"]: d for d in data["designs"]}
                for p in (m or {}).get("points", []):
                    if p["scored"]:
                        continue
                    got = {d["id"]: d for d in data["at"][p["key"]]}
                    for e in m["designs"]:
                        if p["key"] not in e["at"] or e["sha256"] in sized or e["id"] not in got:
                            continue                  # the sizes file's numbers win where it has the design file
                        row, d = e["at"][p["key"]], got[e["id"]]
                        self.assertTrue(d["measured"])
                        self.assertEqual(d["par"], shas.get(e["id"], {}).get("par", False))
                        self.assertEqual(d["m"]["area_um2"], row["area_e4um2"] / 10000)
                        self.assertEqual(d["m"]["time_ps"], row["time_ps"])
                        self.assertEqual(d["m"]["adp"], row["area_e4um2"] * row["time_ps"] / 10_000_000)
                        self.assertEqual(round(d["m"]["area_ge"] * 1000), row["area_mge"])
                        self.assertEqual(d["m"]["depth"], row["depth"])

    def test_every_measured_point_reads_without_javascript(self):
        """Without JavaScript: the explorer is drawn at the scoring size (no note above it: the chart head's tag, shown
        by charts.js at another size, says "not ranked"); every other size has its own table of every design with all
        its numbers, under its heading, in one fold that says measured, not ranked; and the scaling view is drawn by
        the server (wide and compact) for its first metric, one line per design with two points or more, its controls
        hidden until charts.js shows them, with a table of every line at every size, the scored column marked ranked. A
        preview (nothing of it ranked, no par) says so instead, and its scaling view draws the numbers themselves."""
        for t in self.several():
            with self.subTest(task=t):
                preview = t in self.previews
                html_, data = self.page_data(t)
                m = self.measured(t)
                ex = section(html_, "explore")
                self.assertNotIn("data-point-note", ex)
                names = {p["key"]: p["full"] for p in data["points"]}
                scored = next(p for p in data["points"] if p["scored"])
                fold = "every design at the other sizes (measured, not ranked), by score"
                self.assertEqual(norm(text_of(ex)).count(fold), 1)
                body = ex.split(html.escape(fold), 1)[1].split("</details>", 1)[0]
                for p in m["points"]:
                    if p["scored"]:
                        continue
                    head = f'<h3 class="size-head">at {html.escape(names[p["key"]])}</h3>'
                    self.assertIn(head, body)
                    table = body.split(head, 1)[1].split("</table>", 1)[0]
                    for e in m["designs"]:
                        if p["key"] in e["at"] and e["id"] in {d["id"] for d in data["at"][p["key"]]}:
                            d = next(d for d in data["at"][p["key"]] if d["id"] == e["id"])
                            area = d["m"]["area_um2"]
                            s = f"{area:.1f}"
                            if area >= 10000:
                                whole, frac = s.split(".")
                                s = f"{int(whole):,}".replace(",", "\u202f") + "." + frac
                            self.assertIn(f">{s}<", table, (t, e["id"], p["key"]))
                self.assertIn('<div class="explorer-controls" data-scaling-controls hidden>', ex)
                box = ex.split("data-scaling>", 1)[1].split("</figure>", 1)[0]
                self.assertEqual(box.count('<svg class="chart lines'), 2)
                sc = data["scaling"]
                metric = sc["y"]
                if preview:                                 # no par: the numbers themselves
                    self.assertIsNone(sc["par"])
                    drawn = [ln for ln in sc["lines"] if sum(1 for q in ln["pts"] if metric in q["m"]) >= 2]
                else:
                    par = next(ln for ln in sc["lines"] if ln["id"] == sc["par"])
                    base = {q["key"]: q["m"].get(metric) for q in par["pts"]}
                    drawn = [ln for ln in sc["lines"]
                             if sum(1 for q in ln["pts"] if metric in q["m"] and base.get(q["key"])) >= 2]
                wide = box.split('data-size="wide"', 1)[1].split("</svg>", 1)[0]
                self.assertEqual(wide.count('<g class="series"'), len(drawn))
                for ln in drawn:
                    self.assertIn(f'data-id="{html.escape(ln["id"])}"', wide)
                text = norm(text_of(ex))
                if preview:
                    self.assertNotIn('<line class="par-line"', wide)
                    self.assertIn("this task is a preview, so nothing of it is ranked yet", text)
                    self.assertNotIn("the board ranks at", text)
                    self.assertNotIn(", ranked)", text)
                else:
                    self.assertIn('<line class="par-line"', wide)
                    self.assertIn(f"the board ranks at {scored['full']} only", text)
                heads_ = re.findall(r"<th\b[^>]*>(.*?)</th>", ex.split("every design at every point", 1)[1], re.S)
                self.assertEqual([text_of(h) for h in heads_][1:],
                                 [p["full"] + ((" (scored)" if preview else " (ranked)") if p["scored"] else "")
                                  for p in data["points"]])

    def test_shared_lines_and_families_are_explained(self):
        """A line named 'add_n +1' (designs with the same numbers at every point) and a family line ('dadda_ks', one
        fixed-size file per point) are explained under the scaling chart, and only where the page has one."""
        for t in self.several():
            with self.subTest(task=t):
                html_, data = self.page_data(t)
                cap = norm(text_of(section(html_, "explore").split('id="scaling"', 1)[1].split("</figcaption>", 1)[0]))
                lines = data["scaling"]["lines"]
                shared = any(len(ln["names"]) > 1 and not ln["family"] for ln in lines)
                self.assertEqual("stands for that many more designs with the same numbers at every point" in cap, shared)
                fams = sorted(ln["name"] for ln in lines if ln["family"])
                self.assertEqual("of fixed-size baselines, one file per size" in cap, bool(fams))
                for name in fams:
                    self.assertIn(name, cap)

    def test_the_drops_are_said_on_the_page(self):
        """A (design, point) the measurement dropped is named on the page with its reason."""
        for t in self.several():
            with self.subTest(task=t):
                html_, data = self.page_data(t)
                text = norm(text_of(section(html_, "explore")))
                names = {p["key"]: p["full"] for p in data["points"]}
                for e in self.measured(t)["designs"]:
                    for key, why in (e.get("dropped") or {}).items():
                        self.assertIn(f"{e['name']} at {names[key]} ({why})", text)

    def test_compare_references_and_baselines_fold_what_goes_deeper(self):
        """Compare the designs, Proved references and Baselines (2026-11-11): the explorer's count of the designs it
        draws ("k of n designs have both numbers") is hidden while every design has both, and shown when some lack
        one; no note above the chart (2026-11-13: the head's tag says "not ranked" at another size); How the designs scale
        is one closed fold carrying id="scaling"; a task without baselines has no Baselines card and no link to one,
        and one with baselines keeps the card's lead and folds its table."""
        for t in self.listed:
            with self.subTest(task=t):
                html_, _ = self.page_data(t)
                ex = section(html_, "explore")
                counts = re.findall(r'<span data-explorer-note( hidden)?>(\d+) of (\d+) designs have both numbers', ex)
                self.assertTrue(counts)
                for hidden, k, n in counts:
                    self.assertEqual(bool(hidden), k == n, (k, n))
                self.assertEqual(len(re.findall(r"<span data-explorer-note[ >]", ex)), len(counts))
                self.assertNotIn("data-point-note", ex)    # 2026-11-13: no note above the chart; the head's tag
                if 'id="scaling"' in html_:
                    self.assertIn('<details class="scaling-fold" id="scaling"><summary>How the designs scale '
                                  "(measured, not ranked)</summary>", ex)
                    self.assertNotIn('<h3 id="scaling"', html_)
                    self.assertEqual(element_end(ex, ex.index('<details class="scaling-fold"'), "details"),
                                     len(ex.rstrip()))           # the fold ends the card: the scaling view is in it
                baselines = json.loads(self.files[f"data/tasks/{t}.json"])["baselines"]
                if not baselines:
                    self.assertNotIn('id="baselines"', html_)
                    self.assertNotIn('href="#baselines"', html_)
                    self.assertNotIn("No baselines for this task", text_of(html_))
                    continue
                card = section(html_, "baselines")
                fold = card.index("<details><summary>every baseline with its numbers</summary>")
                self.assertTrue(card[:fold].rstrip().endswith("</p>"))
                self.assertIn("Not rankable.", text_of(card[:fold]))
                self.assertLess(fold, card.index("<table"))
                self.assertEqual(card.count("<table"), 1)
                self.assertEqual(element_end(card, fold, "details"), len(card.rstrip()))
        # charts.js keeps the count's rule when it redraws for other axes (no JavaScript runner covers charts.js; the
        # redraw was looked at headless, 2026-11-11)
        with open(os.path.join(SITE, "charts.js"), encoding="utf-8") as fh:
            self.assertIn("note.hidden = r.n >= v.designs.length;", fh.read())

    def test_hidden_tasks_are_not_published(self):
        """A hidden task has no page and no data in the output (none is hidden since 2026-11-08, when matmul and the
        sorter were listed: LatencyTaskTest)."""
        for t, how in self.config["tasks"].items():
            if how != "hidden":
                continue
            with self.subTest(task=t):
                self.assertNotIn(f"tasks/{t}/index.html", self.files)
                self.assertFalse(any(p.startswith(f"tasks/{t}/") or p == f"data/tasks/{t}.json" for p in self.files))

    def test_the_interface_shows_the_header_or_the_ports_never_both(self):
        """Interface (2026-11-11): the module header the design must have, or, for a task whose README has none, its
        ports as a table; not both, since the header holds the same ports, directions and widths."""
        for t in self.listed:
            with self.subTest(task=t):
                iface = section(self.files[f"tasks/{t}/index.html"].decode("utf-8"), "interface")
                header = "Write a module with exactly this header" in iface
                self.assertEqual(iface.count('<th scope="col">port</th>'), 0 if header else 1)
                if header:
                    self.assertEqual(iface.count("<pre"), 1)

    def test_the_trusted_statement_as_property_cards(self):
        """A task with a properties.json shows one card per property and per definition. Each card's
        Lean block is its declaration cut verbatim from the file properties.json names, and its
        "Open in code" lands on that declaration in the source view (Properties.lean's own page, or
        the trusted module's page). The counter counts the properties proper (not the parameter
        range), and the panel says that statement_iff_properties makes the cards the statement."""
        leansrc = build.leansrc
        shown = 0
        for t in self.listed:
            # the lead, above the fold, says that par's design and every accepted record meet the statement (with or
            # without property cards; kept when the statement folded, 2026-11-11; par one design since 2026-11-12)
            lead = section(self.files[f"tasks/{t}/index.html"].decode("utf-8"), "spec").split("</p>", 1)[0]
            self.assertIn("Par's design meets it, and so does every accepted record.", text_of(lead), t)
            pj = os.path.join(SVGOLF, "tasks", t, "properties.json")
            if not os.path.isfile(pj):
                continue
            shown += 1
            with self.subTest(task=t), open(pj, encoding="utf-8") as fh:
                info = json.load(fh)
                here = f"tasks/{t}/index.html"
                spec = section(self.files[here].decode("utf-8"), "spec")
                cards = dict(re.findall(r'<details class="prop" id="([^"]+)">(.*?)</details>', spec, re.S))
                for kind, items in (("prop", info["properties"]), ("def", info["definitions"])):
                    for it in items:
                        body = cards.pop(f"prop-{it['name']}" if kind == "prop" else f"def-{it['decl']}")
                        text = build.read_text(it["file"])
                        block = re.search(r'<pre class="code excerpt"[^>]*><code>(.*?)</code></pre>', body, re.S)
                        lean = text_of(block.group(1))
                        self.assertEqual(lean, leansrc.excerpt(text, leansrc.find(text, it["decl"])), it["decl"])
                        self.assertIn(lean, text)
                        href = re.findall(r'<a class="btn[^"]*" href="([^"]+)"', body)[-1]
                        target, _, frag = href.partition("#")
                        self.assertEqual(frag, it["decl"])
                        dest = posixpath.normpath(posixpath.join(posixpath.dirname(here), target))
                        if it["file"] == info["file"]:
                            self.assertEqual(dest, f"tasks/{t}/properties.html")
                        else:
                            self.assertTrue(dest.startswith("trusted/"), dest)
                        self.assertIn(it["decl"], self.pages[dest].ids)
                self.assertEqual(cards, {})
                n = sum(1 for p in info["properties"] if p["kind"] == "property")
                # a task's page states requirements: no proof status on the cards or in the head
                self.assertNotIn("badge-proved", spec)
                self.assertNotIn("badge-todo", spec)
                self.assertNotIn(">Proved ", spec)
                self.assertIn(f'>Properties<span class="props-n">{n}</span>', spec)
                self.assertIn("theorem statement_iff_properties", text_of(spec))
                # 2026-11-11: the statement is ONE closed fold, right after its lead, holding the panel (Spec.lean
                # and its trusted text too); its summary counts what it holds
                fold_at = spec.index('<details class="spec-fold"')
                self.assertEqual(spec.count('<details class="spec-fold"'), 1)
                self.assertEqual(spec[spec.index("</p>") + len("</p>"):fold_at].strip(), "")
                self.assertTrue(spec.startswith(f'<details class="spec-fold" id="{build.SPEC_FOLD}"><summary>', fold_at))
                fold_end = element_end(spec, fold_at, "details")
                self.assertTrue(fold_at < spec.index('<div class="props" data-tabs') < fold_end)
                self.assertTrue(fold_at < spec.index('<h4 id="closure">') < fold_end)
                # the closure table shows each hash's first 12 digits, and its head says so (2026-11-11)
                closure = spec[spec.index('<h4 id="closure">'):fold_end]
                self.assertIn('<th class="num" scope="col">lines</th><th scope="col">sha256 (first 12)</th>', closure)
                self.assertEqual(spec[fold_end:].strip(), "")
                summary = text_of(spec[fold_at:spec.index("</summary>", fold_at)])
                self.assertIn(f"{n} propert{'y' if n == 1 else 'ies'} · ", summary)
                rejected = section(self.files[here].decode("utf-8"), "does-not-count").count('<p class="reject-head">')
                self.assertIn(f"what does not count ({rejected})", summary)
                self.assertIn((f"tasks/{t}/properties.html", info["file"]),
                              {(f"tasks/{t}/properties.html", src) for src, _ in
                               self.pages[f"tasks/{t}/properties.html"].src_blocks})
                with open(build.repo_file(info["file"]), "rb") as fh:
                    self.assertEqual(self.files[f"tasks/{t}/Properties.lean"], fh.read())
        self.assertGreaterEqual(shown, 5)

    def test_a_recorded_reference_names_its_proof(self):
        """A reference record whose proof is not the par design's (the by-hand proof of the same
        design) says which proof it is, and the explorer's table ("Compare the designs") links it from that proof's
        row (since 2026-11-13 the task page has no Par card)."""
        rec = next(r for r in records() if r["task"] == "add" and r["player"] == self.config["reference_player"])
        with open(os.path.join(SVGOLF, "tasks", "add", "reference", "add_n_byhand.lean"), "rb") as fh:
            self.assertEqual(hashlib.sha256(fh.read()).hexdigest(), rec["files"]["lean"]["sha256"])
        page_ = text_of(self.files[f"tasks/add/records/{rec['record_hash']}.html"])
        self.assertIn("the proof of the reference add_n_byhand", page_)
        self.assertIn("by-hand proof", page_)
        refs = section(self.files["tasks/add/index.html"].decode("utf-8"), "explore")
        row = next(r for r in refs.split("<tr") if "add_n_byhand</" in r)
        self.assertIn(f'href="records/{rec["record_hash"]}.html"', row)
        row = next(r for r in refs.split("<tr") if ">add_n</" in r)
        self.assertNotIn(rec["record_hash"][:12], row)
        self.assertNotIn('id="references"', self.files["tasks/add/index.html"].decode("utf-8"))

    def test_no_internal_why_on_any_page(self):
        """The internal notes of tests/expected.json (`why`) and task.json (`note`, the banlist
        comment where content overrides it) are never rendered; the curated sentences are."""
        with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
            expected = json.load(fh)
        pages = {p: norm(text_of(d)) for p, d in self.files.items() if p.endswith(".html")}
        notes = []
        for t in self.listed:
            exp = expected["tasks"].get(t, {})
            for sec in ("references", "baselines", "negatives", "attacks"):
                notes += [(t, sec, stem, e["why"]) for stem, e in exp.get(sec, {}).items() if e.get("why")]
            task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
            notes += [(t, "note", r["sv"], r["note"]) for r in task.get("references", []) if r.get("note")]
        self.assertTrue(notes)
        for t, sec, stem, why in notes:
            w = norm(why)
            for p, text in pages.items():
                self.assertNotIn(w, text, f"{p} shows the internal note of {t} {sec} {stem}")
        for t in self.listed:
            self.assertNotIn("Refute.lean", pages[f"tasks/{t}/index.html"], t)

    def test_every_rejected_design_has_its_curated_sentence(self):
        with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
            expected = json.load(fh)
        checked = 0
        for t in self.listed:
            with open(os.path.join(SITE, "content", "attacks", f"{t}.json"), encoding="utf-8") as fh:
                said = json.load(fh)
            page_ = norm(text_of(section(self.files[f"tasks/{t}/index.html"].decode("utf-8"), "does-not-count")))
            exp = expected["tasks"].get(t, {})
            for sec in ("negatives", "attacks"):
                for stem, e in exp.get(sec, {}).items():
                    if e.get("advisory") or e.get("stage") == "unproved":
                        continue
                    with self.subTest(task=t, design=f"{sec}/{stem}"):
                        sentence = said.get(sec, {}).get(stem, "")
                        self.assertTrue(sentence.strip(), f"no curated sentence for {t} {sec}/{stem}")
                        self.assertIn(norm(sentence), page_)
                        self.assertIn(f"{stem}.sv ({sec[:-1]}, stopped at {e['stage']})", page_)
                        checked += 1
                for stem in said.get(sec, {}):
                    self.assertIn(stem, exp.get(sec, {}), f"{t}: a curated sentence for an unknown {sec}/{stem}")
        self.assertGreater(checked, 50)

    def test_every_reference_and_baseline_has_its_curated_description(self):
        for t in self.listed:
            with open(os.path.join(SITE, "content", "tasks", f"{t}.json"), encoding="utf-8") as fh:
                info = json.load(fh)
            html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
            self.assertTrue(info.get("title") and info.get("subtitle"), t)
            if self.config["tasks"][t] == "tutorial":       # headed as a tutorial, with no task-id chip (2026-11-12)
                self.assertIn(f"<h1>{html.escape(build.tutorial_title(info['title']))}</h1>", html_)
            else:
                self.assertIn(f"<h1>{html.escape(info['title'])} ", html_)
            data = json.loads(self.files[f"data/tasks/{t}.json"])
            for kind, sec in (("references", None), ("baselines", "baselines")):
                if kind == "baselines" and not data[kind]:    # no baseline, no card (2026-11-11)
                    continue
                for item in data[kind]:
                    # a proof of par's design: on its own page (no Par card on the task page since 2026-11-13)
                    text = norm(text_of(section(html_, sec) if sec else self.files[
                        f"tasks/{t}/records/{item['record_hash']}.html" if item.get("record_hash")
                        else f"tasks/{t}/reference/{item['stem']}.html"]))
                    with self.subTest(task=t, design=item["stem"]):
                        d = info[kind].get(item["stem"], "")
                        self.assertTrue(d.strip())
                        self.assertEqual(item["description"], d.strip())
                        self.assertIn(norm(d), text)

    def test_rejected_designs_are_shown_without_their_comments(self):
        html_ = self.files["tasks/add/index.html"].decode("utf-8")
        part = section(html_, "does-not-count")
        self.assertIn("slang_initial_comb.sv", part)
        self.assertNotIn("data-src", part)
        self.assertNotIn("<span class=\"hl-com\">", part)
        self.assertIn("initial cout", text_of(part))

    def test_a_licensed_rejected_design_keeps_its_notices(self):
        # The SRT attacks are adapted from Apache-2.0 WITH SHL-2.1 code: its copyright and change
        # notices must travel with the code, so these designs are shown with their comments.
        part = text_of(section(self.files["tasks/fdivp/index.html"].decode("utf-8"), "does-not-count"))
        self.assertIn("srt_no_cin.sv", part)
        self.assertIn("SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1", part)
        self.assertIn("Copyright (C) 2021-26 Harvey Mudd College", part)
        self.assertIn("Changes to the Wally code", part)
        self.assertIn("tasks/fdivp/reference/LICENSES/", part)

    def test_an_mit_rejected_design_keeps_its_notice(self):
        # The sorter's attacks are copies of MIT-licensed code (andrewpeck/cell-sort): the MIT notice
        # must be included in every copy, so they are shown with their comments too, each the file byte
        # for byte (its block names it: `data-src`, compared with the file by the verbatim test).
        part = section(self.files["tasks/sorter/index.html"].decode("utf-8"), "does-not-count")
        text = text_of(part)
        self.assertIn("token_self.sv", text)
        self.assertIn("Copyright (c) 2024-2025 Andrew Peck", text)
        self.assertIn("Permission is hereby granted, free of charge", text)
        self.assertIn("The above copyright notice and this permission notice shall be included", text)
        self.assertIn('data-src="svgolf/tests/sorter/attacks/token_self.sv"', part)

    def test_submit_without_a_public_repository(self):
        files = self.files
        if self.config["repo_url"] is not None:
            config = build.load_config()
            config["repo_url"] = None
            files = build.build_site(offline=True, config=config).files
        for t in self.listed:
            with self.subTest(task=t):
                page_ = files[f"tasks/{t}/index.html"].decode("utf-8")
                part = text_of(section(page_, "submit"))
                tutorial = self.config["tasks"][t] == "tutorial"
                self.assertIn("Public submissions open when the svGolf repository is published", part)
                self.assertNotIn("pull request", part)
                self.assertNotIn("git clone", part)
                # the tutorial's part (decided 2026-11-17) says to record WITHOUT --data-dir, after its walk-through's
                # private trial; How to submit elsewhere names no private trial without a public repository
                if tutorial:
                    self.assertIn("record it without --data-dir", part)
                else:
                    self.assertNotIn("--data-dir", part)
                self.assertIn(f"leaderboard/data/{t}/", part)
                self.assertIn("--sandbox require", part)
                self.assertIn("--sandbox auto", part)
                self.assertIn(f"check.py tasks/{t} ", text_of(section(page_, "first-submission")) if tutorial else part)
        self.assertNotIn("pull request", files["llms.txt"].decode("utf-8"))
        # the hand-off in the same words wherever a page says it (decided 2026-11-11): here, the unpublished state's
        for name in ("about.html", "index.html", "roadmap.html"):
            with self.subTest(page=name):
                text = norm(text_of(files[name]))
                self.assertIn(norm(build.HANDOFF_UNPUBLISHED_MD), text)
                for other in (build.HANDOFF_MD, build.HANDOFF_NONE_MD):
                    self.assertNotIn(norm(other), text)
        self.assertIn("Records by pull request", text_of(roadmap_part(files["roadmap.html"], "planned")))
        for name, data in files.items():
            if name.endswith((".html", ".txt", ".md")):
                self.assertNotIn("CI re-verifies", data.decode("utf-8"), name)

    def test_how_to_submit_carries_step0_the_inner_loop_and_the_lean_contract(self):
        """The newcomer study's gaps: every task page says what to install and build first, shows the
        Lean-free inner loop (a clocked task's through the clocked flow, `--seq`), and states the Lean file's
        contract (the generated module, the theorem).

        2026-11-09 (each fact once on a page): each command is on the page once; How to submit points to the "Proving
        a new design" card's Solution.lean rather than show a second skeleton. 2026-11-11 (How to submit is the path of
        a first submission): How to submit holds all four commands; on a page with a card its first two are the
        card's own (the README's, with the options its route uses: one form of each command on the page), with the
        card's text on them, and the card shows none of them; the card is How to submit's last part, below the Lean
        file's fold that points to it. On the tutorial, whose walk-through has Step 0 word for word, How to submit
        points to it (2026-11-11)."""
        unwrap = lambda x: x.replace(" \\\n    ", " ")                     # noqa: E731  (build.wrap_command)
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                tutorial = self.config["tasks"][t] == "tutorial"
                # on the tutorial (decided 2026-11-17: one instruction set) How to submit is its walk-through's last
                # part, "To go public", and the walk-through holds Step 0 and every command
                part = unwrap(text_of(section(html_, "first-submission" if tutorial else "submit")))
                step0_at = section(html_, "first-submission") if tutorial else section(html_, "submit")
                for phrase in ("requirements.txt", "lake build", "score/ppa.py --fetch-liberty"):
                    self.assertIn(phrase, text_of(step0_at))
                self.assertIn('<p id="step-0"><strong>Step 0, once per machine.</strong>', step0_at)
                if tutorial:
                    self.assertNotIn("Step 0, once per machine", text_of(section(html_, "submit")))
                    self.assertNotIn('id="step-0"', section(html_, "submit"))
                    self.assertIn('<section id="submit" class="go-public"><h3>To go public', step0_at)
                has_card = 'id="new-design"' in html_
                card = text_of(section(html_, "new-design")) if has_card else ""
                task = json.loads(read_text_file(f"tasks/{t}/task.json"))
                const = task["statement"]["constant"]
                flow = "--seq --path" if build.metrics.is_clocked(task) else "--no-mapped"
                # a latency kind's Goal takes the latency (build.design_module): matmul and sorter
                goal = ((f"abbrev Goal (lat : …) : Prop :=", f"{const} design.sem lat")
                        if task.get("kind") in build.LATENCY_KINDS else (f"abbrev Goal : Prop := {const} design.sem",))
                for phrase in ("Step 0", f"check.py tasks/{t} solution.sv Solution.lean", "import Submission.Design",
                               "load_design_sv2 design", *goal,
                               "theorem solution : Goal", "theorem Submission.solution : Submission.Goal",
                               "File names and paths are free", "python3.12 leaderboard/leaderboard.py add",
                               f"score/ppa.py solution.sv --task tasks/{t} {flow}", f"check.py tasks/{t} solution.sv "
                               "--unproved", "area_um2_sky130",
                               "the 4-state rules, whether ls-sv can read the design, the post-synthesis simulation",
                               "never accepts", "exits 0 when every"):
                    self.assertIn(phrase, part)
                # each command once on the page, in How to submit (build.commands_once fails the build otherwise)
                page_text = unwrap(text_of(html_))
                # (also without the interpreter: a score tip names the golfing loop's `--path`, not a second form of
                # its command; review 2026-11-11)
                for phrase in (f"python3.12 score/ppa.py solution.sv --task tasks/{t}",
                               f"python3.12 check.py tasks/{t} solution.sv --unproved",
                               f"python3.12 check.py tasks/{t} solution.sv Solution.lean",
                               f"python3.12 leaderboard/leaderboard.py add --task {t}"):
                    if self.config["tasks"][t] != "tutorial":           # its walk-through runs them again
                        self.assertEqual(page_text.count(phrase), 1, phrase)
                        bare = phrase.split(" ", 1)[1]
                        self.assertEqual(len(re.findall(rf"{re.escape(bare)}(?![\w/.-])", page_text)), 1, bare)
                    self.assertNotIn(phrase, card)
                if has_card:
                    # the card's two commands, verbatim but for the line breaks, are How to submit's first two
                    readme = read_text_file(f"tasks/{t}/README.md").split(f"## {build.NEW_DESIGN}\n", 1)[1]
                    fence = readme.split("```bash\n", 1)[1].split("```", 1)[0]
                    for ln in (ln for ln in fence.split("\n") if ln.strip()):
                        self.assertIn(re.split(r"\s{2,}#", ln)[0].strip() + "\n", part)
                    self.assertIn('href="#new-design"', section(html_, "submit"))
                    self.assertNotIn("Solution.lean (a skeleton)", part)       # the card's is the page's one skeleton
                    self.assertRegex(part, r"proves Goal( lat)?, as the (skeleton in The proof in detail|whole "
                                           r"Solution\.lean in Proving a new design), below, shows\.")
                # check.py's usage rule: `--latency` is given exactly for an --unproved run of a latency kind
                # (LatencyTaskTest pins the number)
                unproved = next(ln for ln in part.split("\n") if f"check.py tasks/{t} solution.sv --unproved" in ln)
                self.assertEqual("--latency " in unproved, task.get("kind") in build.LATENCY_KINDS)
                # How to submit's own text names no placeholder file or lemma (`my_`); since 2026-11-11 the card is its
                # last part, whose README skeleton names the player's own lemmas (`my_interface`, ...): not counted
                own = section(html_, "submit")
                if has_card:
                    own = own[:own.index('<section id="new-design"')]
                self.assertNotIn("my_", unwrap(text_of(own)))
                self.assertNotIn("python3 ", part)
        tut = self.files["tasks/_example/index.html"].decode("utf-8")
        walk = text_of(section(tut, "first-submission"))
        for phrase in ("Copy the reference pair", "Score it, no Lean", "--unproved --stage-dir stage",
                       "LEAN_PATH=stage/build lake env lean Probe.lean", "ranked (sky130 A0')", "--data-dir"):
            self.assertIn(phrase, walk)
        self.assertNotIn("TODO", walk)
        # the optional probe step is the walk's one closed fold (2026-11-11); the path's steps stay shown
        steps = section(tut, "first-submission")
        folds = re.findall(r'<li><details class="walk-fold"><summary>(.*?)</summary>(.*?)</details></li>', steps, re.S)
        self.assertEqual([f[0] for f in folds], ["Probe the design (optional: how the tactics read it)"])
        self.assertIn("LEAN_PATH=stage/build lake env lean Probe.lean", text_of(folds[0][1]))

    def test_every_record_page_reproduces_through_its_tasks_flow(self):
        """A record page's "Reproduce and verify" command weighs the design through the flow of its task's kind:
        `ppa.py --seq` (the clocked flow) for a clocked task, whose netlist the comb flow refuses (it prices no
        flip-flop), and no `--seq` for a combinational one."""
        pages = [p for p in self.files if re.fullmatch(r"tasks/[^/]+/records/[0-9a-f]{64}\.html", p)]
        self.assertTrue(pages)
        for p in pages:
            t = p.split("/")[1]
            with self.subTest(page=p):
                part = text_of(section(self.files[p].decode("utf-8"), "reproduce"))
                self.assertIn("python3.12 score/ppa.py ", part)
                seq = build.metrics.is_clocked(json.loads(read_text_file(f"tasks/{t}/task.json")))
                self.assertEqual(f"--task tasks/{t} --seq --path" in part, seq)
                if not seq:
                    self.assertIn(f"--task tasks/{t} --path", part)
                    self.assertNotIn("--seq", part)

    def test_every_ranked_task_has_its_new_design_card(self):
        """Decided 2026-11-05: every ranked task has a "Proving a new design" card (the README's heading and the
        page's, one name since 2026-11-11), the first `## ` section of its README and a part of its page (the same
        text), chosen by the task's kind: the sv_comb route with a
        skeleton for a comb-family task, the one-line `sv_exhaustive` with its assign budget for a comb-fixed
        one; the reactive reduction `ReactTask.satisfiedAt_of_rank` with its rank model, the clocked flow
        (`ppa.py --seq`) and no `--tactics` for a react-family one; each with the layout patterns and the library
        lemmas that exist.

        2026-11-09 (the page stated the task twice): the page's card shows only what no other part of the page says.
        Of the README's opening it shows nothing (or the task's `new_design_lead`), never the opening's restatement of
        the task; the route paragraph; the rest of the README's card (every bold lead-in but the route's) in one
        folded disclosure. So every word the README's card has for the route is still on the page. 2026-11-11: its
        two commands, with what they do, are the first two of How to submit (the path of a first submission), and the
        card's own part is How to submit's last part, not a card of its own."""
        route = {"comb-family": ("sv_structure", "sv_interface", "sv_equations", "sv_cover", "theorem solution : Goal",
                                 "Lay the design out", "Library lemmas that exist today"),
                 "comb-fixed": ("sv_exhaustive", "theorem solution : Goal := by sv_exhaustive", "about 90 assigns",
                                "Library lemmas that exist today"),
                 "react-family": ("ReactTask.satisfiedAt_of_rank", "ReactTask.RankModel", "mooreOut_of_combTargets",
                                  "TerminatesPU.of_invariant", "XSafe", "theorem solution : Goal",
                                  "Lay the design out", "Library lemmas that exist today")}
        for kind, task_type in (("tx-family", "TxTask"), ("stream-family", "StreamTask")):   # matmul, sorter
            route[kind] = (f"{task_type}.satisfiedAtV2_of_phases", f"{task_type}.PhaseModel", "combDeps_of_ffOnly",
                           "TerminatesPU.of_invariant", "XSafe", "theorem solution : Goal lat", "-- svgolf-latency:",
                           "Lay the design out", "Library lemmas that exist today")
        check = {"react-family": "check.py tasks/{t} solution.sv --unproved --stage-dir stage",
                 "tx-family": "check.py tasks/{t} solution.sv --unproved --latency ",
                 "stream-family": "check.py tasks/{t} solution.sv --unproved --latency "}
        ranked = [t for t, how in self.config["tasks"].items() if how == "listed"]
        self.assertGreaterEqual(len(ranked), 5)
        for t in ranked:
            with self.subTest(task=t):
                kind = json.loads(read_text_file(f"tasks/{t}/task.json"))["kind"]
                readme = read_text_file(f"tasks/{t}/README.md")
                self.assertEqual(re.findall(r"^## (.+)$", readme, re.M)[0], "Proving a new design")
                card = norm(text_of(section(self.files[f"tasks/{t}/index.html"].decode("utf-8"), "new-design")))
                for word in route[kind]:
                    self.assertIn(word, card)
                # the card's run without a proof (with the options its route uses) is How to submit's step 1
                submit = norm(text_of(section(self.files[f"tasks/{t}/index.html"].decode("utf-8"), "submit"))
                              .replace(" \\\n    ", " "))
                self.assertIn(check.get(kind, "check.py tasks/{t} solution.sv --unproved --tactics").format(t=t), submit)
                if kind in ("react-family", "tx-family", "stream-family"):
                    self.assertIn(f"score/ppa.py solution.sv --task tasks/{t} --seq --path", submit)
                body = readme.split(f"## {build.NEW_DESIGN}\n", 1)[1].split("\n## ", 1)[0]
                for para in re.findall(r"^\*\*([^*]+)\*\*", body, re.M):     # every bold lead-in, on the page
                    self.assertIn(norm(para), card)
                # decided 2026-11-10: the page opens with the score card, then the two columns starting with "This
                # task", and nothing stands between them; the card is How to submit's last part (2026-11-11), and
                # "How to submit" links it (2026-11-11: "How to participate", which linked it too, is gone: its
                # four steps were How to submit's path a second time)
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                at = [html_.index(mark) for mark in ('id="score"', '<div class="split">', 'label-accent">This task<',
                                                     'id="submit"', 'id="new-design"', 'id="explore"')]
                self.assertEqual(at, sorted(at))
                submit_html = section(html_, "submit")
                sandbox_at = submit_html.index("<summary>the sandbox, and machines without one</summary>")
                self.assertIn('id="new-design"', submit_html[sandbox_at:])
                self.assertNotIn('<section class="card" id="new-design"', html_)
                self.assertEqual(re.findall(r"<section\b[^>]*>", html_[at[0]:at[1]].split("</section>", 1)[1]), [])
                self.assertNotIn('id="participate"', html_)
                self.assertNotIn("How to participate", text_of(html_))
                self.assertIn('href="#new-design"', section(html_, "submit"))
                # the opening's restatement of the task is not on the page: its first sentence is not
                opening = norm(body.split("```", 1)[0])
                info = json.loads(read_text_file(f"site/content/tasks/{t}.json"))
                # the card opens with the task's own opening (new_design_lead, Markdown: its text without the bold
                # marks and with each link's text), else with the route
                self.assertTrue(card.startswith(build.NEW_DESIGN + " #"), card[:80])      # its head and anchor
                opens = card[len(build.NEW_DESIGN + " #"):].lstrip()
                lead = info.get("new_design_lead")
                lead = norm(re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", lead).replace("**", "")) if lead else None
                self.assertTrue(opens.startswith(lead or "The route"), opens[:200])
                for anchor in re.findall(r"\]\([./]*PROVING\.md#([\w-]+)\)", info.get("new_design_lead") or ""):
                    self.assertIn(f'href="../../proving.html#{anchor}"', section(html_, "new-design"))
                # the sentence of the opening that announces the commands is How to submit's (its own words)
                self.assertNotIn("Find the design without Lean", card)
                self.assertIn("find it without Lean and check it once without a proof", submit)
                first = opening.split(". ", 1)[0]
                self.assertTrue(first.startswith("A new "), first)
                self.assertNotIn(first, card)
                self.assertNotIn(first, norm(text_of(html_)))
                # the rest folded: the bold lead-ins after the route are inside the disclosure
                nd = section(html_, "new-design")
                fold_tag = f'<details class="nd-detail" id="{build.NEW_DESIGN_FOLD}">'
                self.assertEqual(nd.count(fold_tag), 1, "no folded part")
                fold_at = nd.index(fold_tag)
                fold_end = element_end(nd, fold_at, "details")
                inside = norm(text_of(nd[fold_at:fold_end]))
                shown = norm(text_of(nd[:fold_at] + nd[fold_end:]))
                after_route = body.split("**The route", 1)[1]
                for para in re.findall(r"^\*\*([^*]+)\*\*", after_route, re.M):
                    self.assertIn(norm(para), inside)
                # 2026-11-11 (reversing review L1/L2, which had the route's step list shown): the step list is the
                # fold's first part, and the fold is the next element after the route paragraph, so the paragraph's
                # closing colon is followed at once by the fold's summary, which names it ("The route step by step");
                # every complete proof the paragraph names has its size in the shown part (the References table's
                # count), the README's or the page's
                route_para = after_route.split("\n\n", 1)[0]
                steps = after_route.split("\n\n", 2)[1]
                if re.match(r"(\d+\.|[-*]) ", steps):
                    first_step = steps.split("\n", 1)[0].split(" ", 1)[1]
                    self.assertNotIn(norm(first_step)[:40], shown)
                    self.assertIn(norm(first_step)[:40], inside)
                    summary = text_of(nd[fold_at:nd.index("</summary>", fold_at)])
                    self.assertIn("The proof in detailThe route step by step · ", summary)
                    route_end = nd.index("</p>", nd.index("<p><strong>The route")) + len("</p>")
                    self.assertEqual(nd[route_end:fold_at].strip(), "")
                if not steps.startswith("```"):
                    for stem in re.findall(r"reference/([\w-]+)\.lean", route_para):
                        n = build.lb.lean_code_lines(read_text_file(f"tasks/{t}/reference/{stem}.lean"))
                        self.assertRegex(shown, rf"(?<![\d,.]){n}(?![\d,.])", stem)
        page_ = self.files["tasks/_example/index.html"].decode("utf-8")
        self.assertNotIn('id="new-design"', page_)              # the tutorial walks through the reference instead

    def test_proving_a_new_design_is_how_to_submits_last_part(self):
        """Decided 2026-11-11: the card is How to submit's last part, under the one name "Proving a new design" (the
        README's heading too): on every listed task with a README card the page has exactly one id="new-design", inside
        #submit, headed "Proving a new design #"; nothing names the card by its former name; the copy of a reference
        adapted from licensed code says to keep its notice; the front page says where the part is."""
        self.assertEqual(build.NEW_DESIGN, "Proving a new design")
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                readme = read_text_file(f"tasks/{t}/README.md")
                self.assertNotIn("Start a new design", html_)
                self.assertNotIn("## Start a new design", readme)
                if f"\n## {build.NEW_DESIGN}\n" not in readme:
                    self.assertNotIn('id="new-design"', html_)
                    continue
                self.assertEqual(html_.count('id="new-design"'), 1)
                submit = section(html_, "submit")
                self.assertEqual(submit.count('<section id="new-design" class="nd-part">'), 1)
                part = section(submit, "new-design")
                head = re.match(r"\s*<h3>(.*?)</h3>", part, re.S)
                self.assertIsNotNone(head, part[:120])
                self.assertEqual(norm(text_of(head.group(1))), "Proving a new design #")
                # the last part: nothing of How to submit follows it
                self.assertTrue(submit.rstrip().endswith("</section>"), submit[-200:])
                self.assertEqual(element_end(submit, submit.index('<section id="new-design"'), "section"),
                                 len(submit.rstrip()))
        sorter = section(self.files["tasks/sorter/index.html"].decode("utf-8"), "submit")
        self.assertIn("Its header carries a licence notice (MIT): keep it in your copy.", norm(text_of(sorter)))
        add = section(self.files["tasks/add/index.html"].decode("utf-8"), "submit")
        self.assertNotIn("licence notice", text_of(add))                      # add's par carries no notice
        home = norm(text_of(self.files["index.html"]))
        self.assertIn('How to submit ends with "Proving a new design"', home)
        self.assertNotIn("Start a new design", home)
        for doc in ("README.md", "PROVING.md", "CONTRIBUTING.md"):
            self.assertNotIn("Start a new design", read_text_file(doc), doc)

    def test_the_right_column_says_only_what_the_task_has(self):
        """2026-11-11 (the task page's declutter): At a glance has a depth budget row only when the task has a budget,
        the banlist's reason folded in a "why" under the banned operators, and the proof time limit in short; Files
        names only cards that hold designs; the Leaderboard's legend names the cycles on a task with a latency (a row's
        middle number). (What moves the score is gone since 2026-11-11: test_no_task_page_has_score_tips.)"""
        factor = build.solution_wall_factor()
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                task = json.loads(read_text_file(f"tasks/{t}/task.json"))
                facts = section(html_, "facts")
                self.assertEqual("depth budget" in text_of(facts), build.lb.effective_depth_budget(task) is not None)
                banned = facts.split(">banned run-time operators</dt><dd>", 1)[1].split("</dd>", 1)[0]
                info = json.loads(read_text_file(f"site/content/tasks/{t}.json"))
                if info.get("banlist_note") or task.get("banlist", {}).get("_comment"):
                    self.assertIn('<details class="reveal"><summary>why</summary>', banned)
                self.assertNotIn("<p", banned.split("<details", 1)[0])
                limit = task["time_limit_s"]
                self.assertIn(f"{limit} s of CPU time (wall-clock backstop {factor * limit:g} s)", text_of(facts))
                files = section(html_, "files")
                for target in re.findall(r'href="#([\w-]+)"', files):
                    self.assertIn("<table", section(html_, target), target)
                # no Par card since 2026-11-13: the Files card links par's own page
                par = lb.par_stem(os.path.join(SVGOLF, "tasks"), task_obj := lb.load_task(os.path.join(SVGOLF, "tasks"), t))
                ref = next(r for r in json.loads(self.files[f"data/tasks/{t}.json"])["references"] if r["stem"] == par)
                dest = (f"records/{ref['record_hash']}.html" if ref.get("record_hash") else f"reference/{par}.html")
                self.assertIn(f'href="{dest}"', files)
                self.assertNotIn('href="#references"', html_)
                legend = re.search(r'<div class="legend-row"><span>(.*?)</span>', section(html_, "leaderboard")).group(1)
                self.assertEqual(legend, "score: area × cycles × clock period, µm²·ns"
                                 if task["kind"] in build.LATENCY_KINDS else "score: area × time, µm²·ns")

    def test_no_task_page_has_score_tips(self):
        """No "What moves the score" card (decided 2026-11-11): its facts are where they belong (the rules' Scoring, the
        golfing loop's comment, the task READMEs), and no content file keeps a `score_tips` key for it."""
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                self.assertNotIn('id="what-moves-the-score"', html_)
                self.assertNotIn("What moves the score", text_of(html_))
        content = os.path.join(SITE, "content", "tasks")
        for name in sorted(f for f in os.listdir(content) if f.endswith(".json")):
            with self.subTest(content=name):
                with open(os.path.join(content, name), encoding="utf-8") as fh:
                    info = json.load(fh)
                self.assertNotIn("score_tips", info)
                self.assertNotIn("What moves the score", info.get("_comment", ""))

    def test_the_task_page_opens_with_the_score_then_the_two_columns(self):
        """The layout decided 2026-11-10: the first box is the score card; directly after it the two-column layout,
        whose left column starts with "This task". No card, list or banner between them: since 2026-11-11 there is no
        quick start (its content is in How to submit) and no in-page contents. The tutorial keeps its step-by-step
        walk-through between the score card and the columns. Since 2026-11-12 How to submit spans the page directly
        under the two columns (in the left column its last part's code ran past the column's edge), and the left
        column is "This task" alone."""
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                def after(sid):
                    """Where the card `<section class="card" id=sid>` ends."""
                    tag = f'<section class="card" id="{sid}">'
                    return html_.index(tag) + len(tag) + len(section(html_, sid)) + len("</section>")
                split_at = html_.index('<div class="split">')
                if self.config["tasks"][t] == "tutorial":
                    # decided 2026-11-17: the tutorial's steps first, then the two columns, then the score card and
                    # the other charts (before, a score chart of one flat line opened the page)
                    head_end = html_.index("</header>", html_.index('<header class="page-head">')) + len("</header>")
                    self.assertTrue(html_.startswith('<section class="card" id="first-submission">', head_end))
                    self.assertEqual(html_[after("first-submission"):split_at], "")
                    self.assertLess(split_at, html_.index('<section class="card" id="score">'))
                    self.assertLess(html_.index('<section class="card" id="score">'),
                                    html_.index('<section class="card" id="explore">'))
                    continue
                end = after("score")
                self.assertEqual(html_[end:split_at], "")
                # the left column: "This task"; How to submit right under the two columns, across the page
                left = html_[split_at:]
                self.assertTrue(left.startswith('<div class="split"><div class="col"><article class="card">'
                                                '<div class="card-head"><div><p class="label label-accent">This task<'),
                                left[:200])
                self.assertIn('</article></div><div class="col">', left)
                self.assertIn('</div></div></div><section class="card" id="submit">', left)
                self.assertLess(left.index('</article></div><div class="col">'), left.index('id="submit"'))
                self.assertNotIn('<section class="card" id="submit">', left.split('</article></div><div class="col">', 1)[0])
                for gone in ('id="quick-start"', '<nav class="toc"', ">Quick start<"):
                    self.assertNotIn(gone, html_)

    def test_a_second_proof_of_pars_design_has_its_numbers(self):
        """Decided 2026-11-17: a second proof of par's design (the tutorial's band_tactics, the pair its walk-through
        copies) has no record of its own, but its design file is par's, byte for byte, and the score reads the design
        file alone: at every size of "Compare the designs" its area, time and score are par's, never a dash where par
        has numbers (before, the scoring size showed a dash)."""
        seen = 0
        for t in self.ranked:
            for pdk in ("sky130", "asap7pnr"):
                if pdk == "asap7pnr" and t in PNR_PAR_PENDING:
                    continue                            # par has no routed numbers yet (PNR_PAR_PENDING)
                explore = section(self.html(f"tasks/{t}/index.html", pdk), "explore")
                rows = [[norm(text_of(c)) for c in re.findall(r"<td\b[^>]*>(.*?)</td>", r, re.S)]
                        for r in re.findall(r"<tr\b[^>]*>(.*?)</tr>", explore, re.S)]
                rows = [r for r in rows if len(r) > 6]
                # a row: the design with its kind ("band_tactics par, another proof"), score, area, time, GE, depth,
                # size, proof lines; par's own row at the same size is the one of the same GE, depth and size
                for r in rows:
                    if not r[0].endswith("par, another proof"):
                        continue
                    with self.subTest(task=t, pdk=pdk, row=r[0], size=r[6]):
                        twins = [p for p in rows if p[0].endswith(" par") and p[4:7] == r[4:7]]
                        self.assertEqual(len(twins), 1, (r, twins))
                        if twins[0][1] == "–":
                            continue
                        seen += 1
                        self.assertEqual(r[1:4], twins[0][1:4])
        self.assertGreater(seen, 0)

    def test_step0_is_complete(self):
        """Decided 2026-11-17 (Step 0 completed, the critique's visitor B): Step 0 on every task page (on the tutorial,
        its walk-through's) says which systems svGolf runs on, that requirements.txt brings the rating build of Yosys
        (since 2026-11-24: the WebAssembly build, the same program on every machine, nothing to build) and how to
        check it (the launcher's self-check, copyable, with the module's sha256: score/reference_build.json), makes a
        virtual environment before pip, names bubblewrap on Linux and `gh` for handing a record in, and says what the
        build costs (time, disk, peak memory) and how long the checks take. llms.txt says the same in short."""
        rb = json.loads(read_text_file("score/reference_build.json"))
        y = rb["yosys"]
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                tutorial = self.config["tasks"][t] == "tutorial"
                at = section(html_, "first-submission") if tutorial else section(html_, "submit")
                step0 = at[at.index('<p id="step-0">'):]
                step0 = step0[:step0.index("Then golf.") if tutorial else step0.index("Then, for each design")]
                text = norm(text_of(step0))
                for said in ("svGolf runs on macOS and Linux; Windows is not supported.",
                             "the same program on macOS and on Linux", "nothing to build, no Yosys on PATH needed",
                             y["self_check"], f"# sha256 {y['sha256']}", f"# version {y['version_line']}",
                             "python3.12 -m venv .venv && . .venv/bin/activate",
                             "bubblewrap (bwrap) with unprivileged user namespaces", "3.75 GB of memory",
                             "about 15 seconds", "about a minute"):
                    self.assertIn(said, text)
                # `gh`, only where a record can be handed in (the public repository and both programs of the route)
                for said in ("gh auth login", "without gh it prints the steps to do by hand"):
                    (self.assertIn if build.submissions_open(self.config) else self.assertNotIn)(said, text)
                self.assertLess(text.index("python3.12 -m venv"), text.index("pip install -r requirements.txt"))
                # the check folds (behind a click) and is a copyable code block
                self.assertIn(f'<details id="{build.YOSYS_RECIPE}"><summary>Check the rating build', step0)
        llms = self.files["llms.txt"].decode("utf-8")
        for said in ("Windows is not supported", y["self_check"], y["sha256"], "python3.12 -m venv .venv"):
            self.assertIn(said, llms)
        (self.assertIn if build.submissions_open(self.config) else self.assertNotIn)("git and gh, logged in", llms)
        self.assertNotIn("from the root of a clone:", llms)

    def test_how_to_submit_is_the_path_of_a_first_submission(self):
        """The second newcomer study (2026-11-10, finding 6): what to run came after about 45,000 characters of a task
        page. Since 2026-11-11 How to submit (across the page under the two columns since 2026-11-12) reads top to
        bottom as a first submission: the two files to write; Step 0; the two `cp` lines that copy par's pair (the reference under
        Files) as the start; the four commands in one block (the golfing loop, the run without a proof, the real
        check, whose comment quotes the INCOMPLETE line the light check prints and calls it expected, the record);
        what "done" is (step 3's `added` line; step 2's accepted is no record); then what the commands do and the
        Lean file. The score card carries one link to it. On the tutorial, whose walk-through copies its own pair,
        How to submit has no copy."""
        unwrap = lambda x: x.replace(" \\\n    ", " ")                     # noqa: E731  (build.wrap_command)
        lb_src = read_text_file("leaderboard/leaderboard.py")
        self.assertIn('print(f"added {args.task}/{rec[\'record_hash\'][:12]}: {rec[\'player\']}, ', lb_src)
        self.assertIn('print("REFUSED: the submission was not added:"', lb_src)
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                submit = section(html_, "submit")
                text = norm(text_of(submit))
                task = json.loads(read_text_file(f"tasks/{t}/task.json"))
                latency = task["kind"] in build.LATENCY_KINDS
                tutorial = self.config["tasks"][t] == "tutorial"
                blocks = [unwrap(html.unescape(re.sub(r"<[^>]+>", "", b)))
                          for b in re.findall(r"<pre\b[^>]*>(.*?)</pre>", submit, re.S)]
                # the two files
                self.assertIn("You hand in two files: solution.sv, a module with the exact header under Interface, and "
                              "Solution.lean, a Lean 4 proof that it meets the trusted statement"
                              + (", at the latency you declare." if latency else "."), text)
                for target in ("#interface", "#spec"):
                    self.assertIn(f'href="{target}"', submit.split("Step 0, once per machine", 1)[0])
                # the copy of par's pair, after Step 0 (the clone) and before the commands
                copies = [b for b in blocks if b.startswith("cp ")]
                cmds = next(b for b in blocks if "leaderboard/leaderboard.py add" in b)
                if tutorial:
                    self.assertEqual(copies, [])
                    self.assertIn("The reference is par's own design, so step 6 above is a private trial: it records "
                                  "nothing on the board.", text)
                else:
                    self.assertEqual(len(copies), 1)
                    refs = task["references"]
                    pair = next(r for r in refs if copies[0] == f"cp tasks/{t}/{r['sv']} solution.sv\n"
                                                                f"cp tasks/{t}/{r['lean']} Solution.lean\n")
                    stem = os.path.splitext(os.path.basename(pair["sv"]))[0]
                    par_note = norm(text_of(section(html_, "numbers"))).split("Record", 1)[0]
                    self.assertIn(stem, par_note)                                       # it is par's pair
                    self.assertIn(f"Start from the reference pair under Files, {stem}, a complete and accepted one", text)
                    self.assertIn('href="#files"', submit)
                # the four commands, in one block, in order; on the tutorial its walk-through ran them, and its last
                # part has the record alone, without --data-dir, with --assisted-by and --notes (decided 2026-11-17)
                lines = [ln for ln in cmds.split("\n") if ln and not ln.startswith("#")]
                if tutorial:
                    self.assertEqual(lines, [f"python3.12 leaderboard/leaderboard.py add --task {t} --player YOUR_HANDLE "
                                             '--assisted-by "TOOL OR MODEL" --sv solution.sv --lean Solution.lean '
                                             '--notes "YOUR DESIGN IN ONE LINE"'])
                    self.assertIn(f"Done: it prints added {t}/HASH: YOUR_HANDLE, … once the pair has passed the whole "
                                  "check, full and sandboxed, and its record is written", text)
                    self.assertIn('Step 5\'s "accepted": true, with its INCOMPLETE line, is feedback for you, not a '
                                  "record.", text)
                    marks = ["You hand in two files", "The reference is par's own design", "Done: it prints",
                             "The Lean file."]
                    at = [text.index(m) for m in marks]
                    self.assertEqual(at, sorted(at), marks)
                    walk = html_.index('id="first-submission"')
                    self.assertLess(walk, html_.index('id="score"'))                  # the steps before the chart
                    self.assertEqual(re.findall(r'<section class="card" id="submit">', html_), [])
                    continue
                # (since 2026-11-25 the golfing loop weighs the design on ASAP7 too: five lines)
                self.assertEqual(len(lines), 5, lines)
                for ln, start in zip(lines, (f"python3.12 score/ppa.py solution.sv --task tasks/{t} ",
                                             f"python3.12 score/ppa.py --pdk asap7 solution.sv --task tasks/{t} ",
                                             f"python3.12 check.py tasks/{t} solution.sv --unproved",
                                             f"python3.12 check.py tasks/{t} solution.sv Solution.lean",
                                             f"python3.12 leaderboard/leaderboard.py add --task {t} ")):
                    self.assertTrue(ln.startswith(start), (ln, start))
                comments = norm(" ".join(ln for ln in cmds.split("\n") if ln.startswith("#")))
                for said in ("# the golfing loop", "# 1. no proof needed; never accepts",
                             '# 2. the real check: prints "accepted": true', '"accepted, but the check was INCOMPLETE '
                             '... # leaderboard.py add runs the full check itself": # expected, step 3 is that command',
                             "# 3. record it: the whole check again, full and sandboxed"):
                    self.assertIn(said, comments)
                # what "done" is: step 3's line; step 2's accepted is no record
                self.assertIn(f"Done: step 3 prints added {t}/HASH: YOUR_HANDLE, … once the pair has passed the whole "
                              "check, full and sandboxed, and its record is written", text)
                self.assertIn("otherwise it prints REFUSED with the reasons and records nothing", text)
                self.assertIn('Step 2\'s "accepted": true, with its INCOMPLETE line, is feedback for you, not a record.',
                              text)
                # the order: the two files, Step 0, the copy, the commands, done, then the explanations and the Lean file
                marks = ["You hand in two files", "Step 0, once per machine"] + ([] if tutorial else ["Start from the "
                                                                                                     "reference pair"])
                marks += ["Then, for each design", "# the golfing loop", "Done: step 3 prints", "The Lean file."]
                at = [text.index(m) for m in marks]
                self.assertEqual(at, sorted(at), marks)
                # facts the page states elsewhere are not repeated here: the score (the Score caption), the latency
                # (the statement's property cards)
                for again in ("Score = area", "the one ranked number", "may take to answer a start"):
                    self.assertNotIn(again, text)
                # the score card's one link to it (not on the tutorial: its walk-through follows the score card)
                score = section(html_, "score")
                links = re.findall(r'<p class="small first-link">(.*?)</p>', score)
                if tutorial:
                    self.assertEqual(links, [])
                else:
                    self.assertEqual(links, ['First submission: <a href="#submit">How to submit</a>'])
                    self.assertEqual(score.count('href="#submit"'), 1)

    def test_step_two_says_the_default_check_is_light(self):
        """check.py's default post-synthesis mode is light (postsynth.DEFAULT_MODE); `leaderboard.py add` runs the
        full one itself (DEFAULT_POSTSYNTH_MODE): step 2 of How to submit, llms.txt and the tutorial say so, so
        that nobody reruns the check in full before recording. Step 3 shows --notes; the handle rule is
        leaderboard.py's."""
        spec = importlib.util.spec_from_file_location("svgolf_postsynth_site", os.path.join(SVGOLF, "check",
                                                                                            "postsynth.py"))
        ps = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ps)
        self.assertEqual(ps.DEFAULT_MODE, "light")
        self.assertEqual(lb.DEFAULT_POSTSYNTH_MODE, "full")
        for t in self.listed:
            with self.subTest(task=t):
                page_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                part = norm(text_of(section(page_, "submit")))
                if self.config["tasks"][t] == "tutorial":           # its walk-through's step 5 says it, then its record
                    walk = norm(text_of(section(page_, "first-submission")))
                    self.assertIn("The post-synthesis check runs LIGHT by default", walk)
                    self.assertIn("accepted, but the check was INCOMPLETE … leaderboard.py add runs the full check "
                                  "itself: expected, the next step is that command", walk)
                    self.assertIn('--notes "YOUR DESIGN IN ONE LINE"', part)
                    self.assertIn(f"It is 1 to {build.handle_max()} characters", part)
                    continue
                self.assertIn("post-synthesis check is LIGHT by default", part)
                self.assertIn("expected, step 3 is that command", part)
                # the line check.py prints for it (incomplete_reasons, then "check: accepted, but ... INCOMPLETE")
                self.assertIn('so stderr also says # "accepted, but the check was INCOMPLETE ... # leaderboard.py add '
                              'runs the full check itself": # expected', part)
                self.assertIn('--notes "YOUR DESIGN IN ONE LINE"', part)
                self.assertIn(f"It is 1 to {build.handle_max()} characters", part)
        self.assertTrue(lb.PLAYER_RE.fullmatch("a" * build.handle_max()))
        self.assertFalse(lb.PLAYER_RE.fullmatch("a" * (build.handle_max() + 1)))
        self.assertIn("post-synthesis check is LIGHT by default", self.files["llms.txt"].decode("utf-8"))
        walk = norm(text_of(section(self.files["tasks/_example/index.html"].decode("utf-8"), "first-submission")))
        self.assertIn("The post-synthesis check runs LIGHT by default", walk)
        check_src = read_text_file("check.py")
        for said in ("accepted, but the check was INCOMPLETE", "leaderboard.py add runs the full check itself"):
            self.assertIn(said, check_src)
            self.assertIn(said, walk)
            self.assertIn(said, self.files["llms.txt"].decode("utf-8"))

    def test_llms_txt_names_each_task_s_best_submission(self):
        """llms.txt's "best submission" and data/site.json's `best` are the players' best record by area × time, the
        first row of their board's ranking (data/tasks/<t>.json `submissions_board`), not the smallest area."""
        summary = {x["name"]: x for x in json.loads(self.files["data/site.json"])["tasks"]}
        llms = self.files["llms.txt"].decode("utf-8")
        for t in self.ranked:
            with self.subTest(task=t):
                board = json.loads(self.files[f"data/tasks/{t}.json"])["submissions_board"]
                best = summary[t]["best"]
                if not board["ranking"]:
                    self.assertIsNone(best)
                    continue
                top = board["ranking"][0]
                self.assertEqual((best["record_hash"], best["time_ps"]), (top["record_hash"], top["time_ps"]))
                line = next(ln for ln in llms.split("\n") if f"(`{t}`)" in ln)
                self.assertIn(f"best submission {build.lb.fmt_um2(top['area_e4um2'])} um^2, {top['time_ps']} ps", line)
        mm = json.loads(self.files["data/tasks/matmul.json"])["submissions_board"]
        self.assertGreater(len(mm["frontier"]), 1)                # the case that told the two apart
        self.assertNotEqual(mm["frontier"][0]["record_hash"], summary["matmul"]["best"]["record_hash"])
        # the routed course's block of data/site.json follows the same rule on its board
        for t in self.ranked:
            with self.subTest(task=t, pdk="asap7pnr"):
                board = json.loads(self.files[f"data/tasks/{t}.json"])["asap7pnr"]["submissions_board"]
                best = summary[t]["asap7pnr"]["best"]
                if not board["ranking"]:
                    self.assertIsNone(best)
                    continue
                top = board["ranking"][0]
                self.assertEqual((best["record_hash"], best["time_ps"], best["best_time_ps"]),
                                 (top["record_hash"], top["time_ps"], min(r["time_ps"] for r in board["ranking"])))
        a7 = json.loads(self.files["data/tasks/matmul.json"])["asap7pnr"]["submissions_board"]
        self.assertGreater(len(a7["frontier"]), 1)
        self.assertNotEqual(a7["frontier"][0]["record_hash"], summary["matmul"]["asap7pnr"]["best"]["record_hash"])

    def test_no_record_page_diffs_against_an_earlier_record(self):
        """Decided 2026-11-13 (the owner's UI feedback): a record page shows no diff against the previous frontier
        record (a reader diffs the downloads if they want to), and its facts no longer name a previous frontier."""
        for r in records():
            with self.subTest(record=r["record_hash"][:12]):
                h = self.files[f"tasks/{r['task']}/records/{r['record_hash']}.html"].decode("utf-8")
                self.assertNotIn('id="diff"', h)
                self.assertNotIn('class="code diff"', h)
                self.assertNotIn("Against the previous frontier record", h)
                self.assertNotIn("<dt>previous frontier</dt>", h)
        self.assertFalse(hasattr(build, "diff_html"))
        self.assertFalse(hasattr(build, "previous_frontier_record"))

    def test_writeups_and_notes_link_the_designs_they_name(self):
        """Decided 2026-11-23 (the owner's feedback on the best mul record's writeup, which named the two-row-leaf
        tree `mul_tree_h` without a link, a design whose only board record is later than the writeup's own): (1) in a
        record page's writeup, and in its notes and assisted-by rows, every paragraph that names another design or
        record links it in that paragraph: a reference design of tasks/*/reference/ (its stem, with .sv or .lean, or
        alone when the stem holds an underscore), another record's design file (`core_mesh_late.sv`), a record hash,
        a player, or par's design ("the reference", "the ... reference", "par's"; on par's own records these mean the
        record itself; "the ... reference variant" is a variant of it, a record named by its own link). A link counts when it goes to that record's page, to the file or page of that design on the
        site or in the repository (the repository address `repo_link` gives, or, in a tree with no public address,
        the span.unlinked the site writes in its place), or to a record whose design file is that design byte for
        byte. (2) Every link to a record submitted after the page's own carries the class writeup.BOARD_SINCE and is
        followed by "(on the board since <its date>)", so a later record is never presented as a predecessor."""
        recs = {r["record_hash"]: r for r in records()}
        refs = {}                                     # stem -> (task, sha256 of its .sv)
        for f in sorted(glob.glob(os.path.join(SVGOLF, "tasks", "*", "reference", "*.sv"))):
            with open(f, "rb") as fh:
                refs[os.path.basename(f)[:-3]] = (f.split(os.sep)[-3], hashlib.sha256(fh.read()).hexdigest())
        with open(os.path.join(SVGOLF, "leaderboard", "par.json"), encoding="utf-8") as fh:
            par = {t: v["design"] for t, v in json.load(fh)["par"].items()}
        players = sorted({r["player"] for r in recs.values()}, key=len, reverse=True)
        repo_url = self.config.get("repo_url")
        problems = []
        for h, rec in sorted(recs.items()):
            here = f"tasks/{rec['task']}/records/{h}.html"
            page_html = self.files[here].decode("utf-8")
            parts = []
            if 'class="writeup-body"' in page_html:
                parts.append(("writeup", page_html[page_html.index('class="writeup-body"'):
                                                   page_html.index("</section>", page_html.index('class="writeup-body"'))]))
            for row in ("notes", "assisted by"):
                m = re.search(rf"<dt>{row}</dt><dd>(.*?)</dd>", page_html, re.S)
                parts.append((row, f"<dd>{m.group(1)}</dd>"))
            # (1) is the maintainers' rule for their own text: a player outside the maintainers (build.OUTSIDE_PLAYERS,
            # since 2026-11-24) wrote its writeup, notes and assisted-by itself, and the maintainers do not rewrite a
            # player's text; (2) is the site's own marking of a link and holds on every page
            own_text = rec["player"] not in build.OUTSIDE_PLAYERS
            for where, part in parts:
                for blk in _Blocks.of(part):
                    targets = [_link_target(here, a, repo_url) for a in blk["links"]]
                    for name in (_names_in(blk["text"], rec, recs, refs, players, self.config["reference_player"])
                                 if own_text else ()):
                        if not _named_linked(name, rec, recs, refs, par, targets):
                            problems.append(f"{rec['task']} {h[:12]} {where}: {name} unlinked in: "
                                            f"{norm(blk['text'])[:120]}")
                    for a, (kind, path) in zip(blk["links"], targets):
                        m = re.fullmatch(r"tasks/[^/]+/records/([0-9a-f]{64})\.html", path or "")
                        if kind != "site" or not m:
                            continue
                        date = recs[m.group(1)]["submitted_at"][:10]
                        if date > rec["submitted_at"][:10] and not (
                                build.writeup.BOARD_SINCE in a["cls"].split()
                                and a["after"].startswith(build.writeup.board_since_text(date))):
                            problems.append(f"{rec['task']} {h[:12]} {where}: links the later record "
                                            f"{m.group(1)[:12]} ({date}) without \"on the board since\"")
        self.assertEqual(problems, [], "\n".join(problems))

    def test_a_record_with_a_writeup_shows_its_notes_first_sentence(self):
        """Decided 2026-11-25 (the owner, of a record page with a note of about 2000 characters and no writeup: "That
        could probably be moved"): a record page whose record has a writeup shows its note's first sentence and a link
        to the Writeup tab, the whole note folded under them (the note stays: it is part of the record's hash); a
        record without a writeup shows its whole note, as before. Every note longer than 300 characters now has a
        writeup."""
        wdir = os.path.join(SVGOLF, "leaderboard", "writeups")
        folded = long_ = 0
        for r in records():
            h = r["record_hash"]
            notes = (r.get("notes") or "").strip()
            with self.subTest(record=h[:12]):
                page_html = self.files[f"tasks/{r['task']}/records/{h}.html"].decode("utf-8")
                dd = re.search(r"<dt>notes</dt><dd>(.*?)</dd>", page_html, re.S).group(1)
                if not notes:
                    self.assertEqual(norm(text_of(dd)), "none")
                    continue
                if not os.path.isfile(os.path.join(wdir, h + ".html")):
                    self.assertLessEqual(len(notes), 300)
                    self.assertNotIn('href="#writeup"', dd)
                    self.assertNotIn("<details", dd)
                    self.assertEqual(norm(text_of(dd)), norm(notes))
                    continue
                long_ += len(notes) > 300
                first, rest = build.note_parts(notes)
                lead = dd.split("<details", 1)[0]
                if h in build.NOTE_LEADS:                # re-labelled (below): the maintainers' words, marked
                    first, rest = build.NOTE_LEADS[h] + " " + build.NOTE_LEAD_MARK, rest or notes
                self.assertEqual(norm(text_of(lead)), norm(first + " More in the writeup."))
                self.assertIn('<span class="note-more">More in <a href="#writeup">the writeup</a>.</span>', lead)
                if rest:
                    folded += 1
                    fold = dd[len(lead):]
                    self.assertTrue(fold.startswith('<details class="reveal note-whole"><summary>the whole note'
                                                    '</summary>'), fold[:120])
                    self.assertEqual(norm(text_of(fold.split("</summary>", 1)[1])), norm(notes))
                else:
                    self.assertNotIn("<details", dd)
        self.assertEqual(long_, 33)
        self.assertGreaterEqual(folded, 33)
        # the sentence rule: a sentence ends after a word, not at a dot product's " . "
        self.assertEqual(build.note_parts("Adds A[i][k] . B[k][j] per cycle. Then C."),
                         ("Adds A[i][k] . B[k][j] per cycle.", "Then C."))
        self.assertEqual(build.note_parts("one line, latency ceil(N/2) = 2 at N=4"),
                         ("one line, latency ceil(N/2) = 2 at N=4", ""))

    def test_the_seven_product_tile_is_named_for_its_scored_size(self):
        """Decided 2026-11-25 (the owner agreed to re-label it as what it is at the scored size): record 2ca5fe4fe656
        stores the seven Strassen products only at N = 2 and is par's schoolbook multiply-accumulate schedule at every
        other N, the scoring point N = 4 included, so wherever the site names its architecture (its title: the record
        page's heading, the board's row, the charts) it says so; its record and design file are unchanged. Record
        43b794c93301, one level of Strassen at every N with schoolbook block engines, says "one level"."""
        title = "Schoolbook multiply-accumulate; Strassen only at N = 2"
        h = next(r["record_hash"] for r in records() if r["record_hash"].startswith("2ca5fe4fe656"))
        page_html = self.files[f"tasks/matmul/records/{h}.html"].decode("utf-8")
        self.assertEqual(text_of(re.search(r"<h1\b[^>]*>(.*?)</h1>", page_html, re.S).group(1)), title)
        writeup_ = norm(text_of(page_html[page_html.index('class="writeup-body"'):]))
        self.assertIn("At the scored size, N = 4, this design is a schoolbook multiply-accumulate schedule, the "
                      "structure of par's design; its seven-product (Strassen) tile applies only at N = 2.", writeup_)
        # its notes row leads with the maintainers' words, marked as theirs; the record's own note is under the fold
        self.assertEqual(list(build.NOTE_LEADS), [h])
        dd = re.search(r"<dt>notes</dt><dd>(.*?)</dd>", page_html, re.S).group(1)
        lead, fold = dd.split("<details", 1)
        self.assertEqual(norm(text_of(lead)), "At the scored size, N = 4, a schoolbook multiply-accumulate schedule; "
                         "its seven-product (Strassen) tile applies only at N = 2. (the maintainers' summary; the "
                         "record's note is below) More in the writeup.")
        rec = next(r for r in records() if r["record_hash"] == h)
        self.assertEqual(norm(text_of(fold.split("</summary>", 1)[1])), norm(rec["notes"]))
        board = self.files["tasks/matmul/index.html"].decode("utf-8")
        row = re.search(rf'href="records/{h}\.html">[^<]*</a><span class="board-title">([^<]*)</span>', board)
        self.assertEqual(html.unescape(row.group(1)), title)
        self.assertIn(f'aria-label="{html.escape(title)}"', board)
        g = next(r["record_hash"] for r in records() if r["record_hash"].startswith("43b794c93301"))
        other = self.files[f"tasks/matmul/records/{g}.html"].decode("utf-8")
        self.assertIn("one level", text_of(re.search(r"<h1\b[^>]*>(.*?)</h1>", other, re.S).group(1)))

    def test_every_guide_says_to_measure_both_libraries(self):
        """Decided 2026-11-25 (the owner: "I would like all agents to run asap7 as well as sky130"): Step 0 fetches the
        five pinned ASAP7 files, the golfing loop weighs a design on ASAP7 too, and step 3 says `add` measures both;
        in How to submit, llms.txt and README's Quick start."""
        fetch = "python3.12 score/ppa.py --pdk asap7 --fetch-liberty"
        unwrap = lambda x: x.replace(" \\\n    ", " ")                     # noqa: E731  (build.wrap_command)
        for t in ("add", "matmul"):
            with self.subTest(task=t):
                part = unwrap(text_of(section(self.files[f"tasks/{t}/index.html"].decode("utf-8"), "submit")))
                self.assertIn(fetch, part)
                flag = "--seq" if t == "matmul" else "--no-mapped"
                self.assertIn(f"python3.12 score/ppa.py --pdk asap7 solution.sv --task tasks/{t} {flag}", part)
                self.assertIn("then the ASAP7 columns too (both libraries)", part)
                self.assertIn("--notes is one optional line (at most 300 characters since 2026-11-25", norm(part))
        llms = self.files["llms.txt"].decode("utf-8")
        self.assertIn(fetch, llms)
        self.assertIn("python3.12 score/ppa.py --pdk asap7 solution.sv --task tasks/add --no-mapped", llms)
        readme = read_text_file("README.md")
        quick = readme[readme.index("## Quick start"):readme.index("## Rules")]
        self.assertIn(fetch, quick)
        self.assertIn("python3.12 score/ppa.py --pdk asap7 solution.sv --task tasks/add --no-mapped", quick)
        self.assertIn("It measures both libraries", quick)
        contributing = read_text_file("CONTRIBUTING.md")
        self.assertIn(fetch, contributing)

    def test_home_defines_under_par_and_the_clocked_time(self):
        html_ = self.files["index.html"].decode("utf-8")
        # the note on par, record and under par is the rules page's since 2026-11-13 (the front page's block over the
        # cards is its heading alone); every footer links it ("How it is scored")
        self.assertNotIn('class="course-note"', html_)
        rules = norm(text_of(self.files["rules.html"]))
        self.assertIn("Under par is how far the record is below par, as a share of par's score", rules)
        self.assertIn('href="rules.html#courses">How it is scored</a>', html_)
        lead = norm(text_of(html_[html_.index('class="hero-lead"'):html_.index('class="btn-row"')]))
        self.assertIn("on a clocked task, the time is the clock period, times the latency in cycles", lead)
        # how a record reaches the board, in the one sentence of this build's state (decided 2026-11-11)
        self.assertIn(norm(build.handoff_md(self.config)), norm(text_of(html_)))

    def test_the_claims_on_home_and_about_hold(self):
        """Decided 2026-11-11 (the publication review): the front page and About claim only what holds. About says the
        escape designs are listed under "What does not count", each with the stage that refuses it (every listed task
        page has the pane and says so), not that each has a kernel-checked refutation, and it calls the statements'
        authors the maintainers; home's "the same file always scores the same" is on the rating build; the random
        vectors' salt is described as it is (no record so far was checked with one: the records are read here); and
        the line on who made the records so far is the rules page's (README's Leaderboard, in build.py's words; since
        2026-11-13 not the front page's, whose block over the task cards is its heading alone)."""
        home_html = self.files["index.html"].decode("utf-8")
        home, about = norm(text_of(home_html)), norm(text_of(self.files["about.html"]))
        for stale in ("kernel-checked refutations", "salted in competition runs", "the same file always scores the same (",
                      "organizers"):
            self.assertNotIn(stale, home)
            self.assertNotIn(stale, about)
        self.assertIn('under "What does not count", a tab of the trusted statement, each with the checker stage that '
                      "refuses it.", about)
        for t in self.listed:
            with self.subTest(task=t):
                pane = norm(text_of(section(self.files[f"tasks/{t}/index.html"].decode("utf-8"), "does-not-count")))
                self.assertIn("The checker stops at the first stage that refuses; each design is listed with that "
                              "stage.", pane)
        self.assertIn("The same file scores the same on every machine, byte for byte: the rating build is one "
                      "WebAssembly program (a native Yosys can differ: reproduce a score)", home)
        # the salt clause is the records' (decided 2026-11-12: whatever a new record says, the page stays true): every
        # record says of each run whether it was salted, and the front page says what they say
        recs = records()
        for r in recs:
            salts = build.record_salts(r)
            self.assertTrue(salts, r["record_hash"])
            self.assertTrue(all(isinstance(x, bool) for x in salts), r["record_hash"])
        self.assertIn(f"seeded random vectors (a secret salt can make them unpredictable; {build.salt_md(recs)})", home)
        self.assertEqual(build.salt_md([]), "the board's records so far were checked without one")
        salted = {"postsynth": {"salted": True}}
        clocked = {"postsynth": {"points": [{"seeds": [{"salted": False}, {"salted": True}]}]}}
        self.assertEqual(build.salt_md([salted]), "one of the board's records was checked with one (its page says so)")
        self.assertEqual(build.salt_md([salted, clocked, {"postsynth": {"salted": False}}]),
                         "some of the board's records were checked with one (its page says so)")
        head = home_html[home_html.index('<div class="section-head" id="tasks">'):home_html.index('<ul class="task-cards">')]
        self.assertEqual(head, '<div class="section-head" id="tasks"><h2>Tasks</h2></div>')
        rules = norm(text_of(self.files["rules.html"]))
        self.assertIn(norm(build.FIRST_ENTRIES_MD), rules)
        first = "Outside entries come in by pull request; the first came on 2026-11-24."
        self.assertEqual(home.count(first), 0)
        self.assertEqual(rules.count(first), 1)
        self.assertNotIn("There are no outside entries yet.", rules)
        # the claim holds against the records (decided 2026-11-25, with the first outside records): the earliest
        # record of a player outside the maintainers is dated 2026-11-24
        outside = [r for r in recs if r["player"] in build.OUTSIDE_PLAYERS]
        self.assertTrue(outside)
        self.assertEqual(min(str(r["submitted_at"])[:10] for r in outside), "2026-11-24")

    def test_shown_paths_are_the_public_repositorys(self):
        """Decided 2026-11-11: the public repository is svGolf's own tree, so a path of it is shown as that repository
        shows it, without this tree's `svgolf/` (page.shown_path): the property cards' paths, the statement's path and
        its trusted text on a task page, the "file" of a properties page and of a trusted page (and their boxes' names),
        the shared trusted base's table, the rules' and the reproduce page's sources. The library's own paths are
        unchanged. No footer shows a path. The refusals page's reading list names no path at all (2026-11-13): it says
        what each document holds and links it where the build has an address."""
        self.assertEqual(build.shown_path("svgolf/tasks/add/Spec.lean"), "tasks/add/Spec.lean")
        self.assertEqual(build.shown_path("LeanModels/Sv/Ast.lean"), "LeanModels/Sv/Ast.lean")
        seen = {"prop-path": 0, "file": 0}
        web = build.repo_web(self.config.get("repo_url"))     # the public tree's (the export sets it): its addresses
        for path, data in sorted(self.files.items()):
            if not path.endswith(".html"):
                continue
            h = data.decode("utf-8")
            with self.subTest(page=path):
                foot = h.split('<footer class="site-footer">', 1)[1]
                if web:                     # a link into the public repository is an address, not a path it shows
                    foot = re.sub(rf'href="{re.escape(web)}(?:/[^"]*)?"', 'href=""', foot)
                self.assertNotIn("svgolf/", foot)
                self.assertNotIn("generated by", foot)
                for span in re.findall(r'<div class="prop-path"><span>(.*?)</span>', h):
                    seen["prop-path"] += 1
                    self.assertFalse(text_of(span).startswith("svgolf/"), span)
                for meta in re.findall(r'<span class="cell-meta">(.*?)</span>', h):
                    self.assertFalse(text_of(meta).startswith("svgolf/"), meta)
                for name in re.findall(r'<span class="codebox-name">(.*?)</span>', h):
                    self.assertFalse(text_of(name).startswith("svgolf/"), name)
                for value in re.findall(r"<dt>file</dt>\s*<dd>(.*?)</dd>", h, re.S):
                    seen["file"] += 1
                    self.assertFalse(text_of(value).startswith("svgolf/"), value)
        self.assertGreater(seen["prop-path"], 0)
        self.assertGreater(seen["file"], 0)
        shared = self.files["trusted/index.html"].decode("utf-8")
        self.assertIn("<code>SvGolf/Task.lean</code>", shared)
        self.assertNotIn("<code>svgolf/", shared)
        self.assertIn("From <code>README.md</code> of the repository", self.files["rules.html"].decode("utf-8"))
        self.assertIn("From <code>score/PPA.md</code> of the repository", self.files["reproduce.html"].decode("utf-8"))
        refusals = self.files["refusals.html"].decode("utf-8")
        more = refusals[refusals.index('<h2 id="more">'):]
        more = more[:more.index("</ul>")]
        self.assertNotIn("<code>", more)
        self.assertNotIn("svgolf/", text_of(more))
        lib = self.config["library"]
        self.assertIn(f'href="{lib["url"]}/blob/HEAD/docs/sv-refusals.md"', more)
        self.assertIn('href="rules.html#checker-stages"', more)
        if web:                             # the full register's rendering, in the public repository
            self.assertIn(f'href="{web}/blob/HEAD/REFUSALS.md"', more)
        sub = text_of(re.search(r'<p class="head-sub">(.*?)</p>', refusals, re.S).group(1))
        self.assertIn(f"checked against the refusal register of {lib['name']} at the revision svGolf uses", sub)
        self.assertNotIn("lean-surfaces", sub)

    def refusals_visible(self):
        """The Refusals page's main text outside its folds (`<details>`), and the whole main text."""
        h = self.files["refusals.html"].decode("utf-8")
        main = h[h.index("<main"):h.index("</main>")]
        visible = main
        while "<details" in visible:
            visible = re.sub(r"<details\b(?:(?!<details\b).)*?</details>", "", visible, flags=re.S)
        return text_of(visible), text_of(main)

    def test_the_refusals_page_reads_in_plain_words(self):
        """Decided 2026-11-13 (the Refusals page's round): outside its folds the page has no internal code (a refusal
        register row id, a principle id, a language-tier node kind, a work-package code), no file path and no plan
        word; the codes are behind each card's fold. Anywhere on the page, the folds included: no plan file, no
        work-package code, no internal statement name (people's names are the private denylist's, which the strict
        build and the export's scan apply; this tree never spells them)."""
        visible, whole = self.refusals_visible()
        reg = json.loads(build.read_text(self.config["refusals_json"]))
        codes = {e["id"] for e in reg["entries"] + reg["svgolf"]["entries"]} | {p["id"] for p in reg["principles"]}
        content = json.loads(read_text_file("site/content/refusals.json"))
        ls_rows = {e["id"]: e for e in reg["entries"]}
        on_page = {i for g in content["groups"] for c in g["cards"] for i in c["rows"]}
        codes |= {ls_rows[i]["tag"] for i in on_page if i in ls_rows}          # node kinds: ConversionExpression:width
        for c in sorted(codes):
            with self.subTest(code=c):
                self.assertIsNone(re.search(rf"(?<![\w-]){re.escape(c)}(?![\w-])", visible), c)
        self.assertIsNone(re.search(r"\b[A-Z][A-Za-z]*(?:Expression|Statement|Symbol)(?::\w+)?\b", visible))
        self.assertIsNone(re.search(r"(?:[\w.-]+/)+[\w.-]+\.[A-Za-z]{1,5}\b", visible), "a file path")
        self.assertIsNone(re.search(r"\b[\w-]+\.(?:py|lean|json|md|ys|sv|txt)\b", visible), "a file name")
        for word in ("WP-", "WP5", "PLAN", "plan item", "work package", "work-package", "txtask", "organizer",
                     "run2", "lean-surfaces", "awaiting", "to confirm", "v0", "ls-sv", "register row"):
            with self.subTest(word=word):
                self.assertNotIn(word, visible)
        for word in ("WP-", "PLAN.md", "txtask-v", "organizer", "run2"):
            with self.subTest(anywhere=word):
                self.assertNotIn(word, whole)

    def test_every_refusal_card_shows_a_refused_line_and_what_to_write_instead(self):
        """Every card of the Refusals page (content/refusals.json) shows its construct's name, one refused example and
        what to write instead (code, or a sentence), and names the refusal register's rows behind its fold; every
        svGolf row of the register but the aggregates is on the page exactly once, on a card or in a group's fold, and
        a card's state line says only what all its rows say."""
        content = json.loads(read_text_file("site/content/refusals.json"))
        h = self.files["refusals.html"].decode("utf-8")
        found = re.findall(r'<article class="refusal">(.*?)</article>', h, re.S)
        cards = [c for g in content["groups"] for c in g["cards"]]
        self.assertEqual(len(found), len(cards))
        self.assertGreaterEqual(len(cards), 20)
        reg = json.loads(build.read_text(self.config["refusals_json"]))
        rows = {e["id"]: e for e in reg["entries"] + reg["svgolf"]["entries"]}
        for c, card in zip(cards, found):
            with self.subTest(card=c["title"]):
                self.assertTrue(c["title"].strip())
                self.assertIn(norm(c["title"]), norm(text_of(re.search(r"<h3[^>]*>(.*?)</h3>", card, re.S).group(1))))
                shown, fold = card.split("<details", 1)
                self.assertIn('<p class="refusal-label refusal-no">Refused</p>', shown)
                self.assertIn('<p class="refusal-label refusal-yes">Write instead</p>', shown)
                blocks = [text_of(b) for b in re.findall(r"<pre\b[^>]*>(.*?)</pre>", shown, re.S)]
                self.assertEqual(blocks[0], c["refused"].rstrip())
                if c.get("instead"):
                    self.assertEqual(blocks[1:], [c["instead"].rstrip()])
                else:
                    self.assertEqual(len(blocks), 1)
                    self.assertTrue(c["instead_text"].strip())
                    self.assertIn(norm(c["instead_text"]), norm(text_of(shown)))
                self.assertTrue(c["rows"])
                for i in c["rows"]:
                    self.assertIn(f"<code>{i}</code>", fold)
                cats = {rows[i]["category"] for i in c["rows"]}
                state = re.search(r'<p class="refusal-state">(.*?)</p>', shown, re.S)
                if len(cats) == 1 and cats <= {"later", "never"}:
                    self.assertEqual(text_of(state.group(1)), build.REFUSAL_CARD_STATE[cats.pop()])
                else:
                    self.assertIsNone(state)
        for e in reg["svgolf"]["entries"]:
            with self.subTest(row=e["id"]):
                self.assertEqual(h.count(f"<code>{e['id']}</code>"), 0 if e.get("aggregate") else 1)

    def test_the_footer_is_for_visitors(self):
        """Decided 2026-11-11: every page's footer is one row of links for a visitor: the licence (Apache-2.0), the
        public repository's source, issues and contributing guide (when the repository is named), the Lean library,
        the roadmap, how to reproduce a score, llms.txt and the data, and the revision. Without a public repository the
        licence is plain text and nothing links to a repository; About says where questions go in both builds. The
        build under test is the tree's own: the development tree's (no `repo_url`) or the public tree's (the export
        sets it), and a public build made here in memory with another address. Each link is a 24 px tap target
        (decided 2026-11-12; WCAG 2.2, 2.5.8): style.css's rule for them sets the height."""
        css = read_text_file("site/style.css")
        rule = re.search(r"^\.foot-links a \{([^}]*)\}", css, re.M).group(1)
        self.assertIn("display: inline-flex;", rule)
        self.assertIn("min-height: 24px;", rule)

        def foot(h):
            return h.split('<ul class="foot-links">', 1)[1].split("</ul>", 1)[0]

        def public(files, web, build_name):
            for path, data in sorted(files.items()):
                if path.endswith(".html"):
                    with self.subTest(page=path, build=build_name):
                        f = foot(data.decode("utf-8"))
                        licence = build.repo_link(web, "svgolf/LICENSE" if build.LAYOUT == "standalone" else "LICENSE")
                        self.assertTrue(f.startswith(f'<li><a href="{licence}">Apache-2.0</a></li>'), f[:120])
                        self.assertIn(f'<li><a href="{web}">Source</a></li>', f)
                        self.assertIn(f'<li><a href="{web}/issues">Issues</a></li>', f)
                        self.assertIn(f'<li><a href="{build.repo_link(web, "svgolf/CONTRIBUTING.md")}">Contributing'
                                      '</a></li>', f)
                        root = build.root_of(path)
                        for label, href in (("How it is scored", "rules.html#courses"), ("Roadmap", "roadmap.html"),
                                            ("Reproduce a score", "reproduce.html"),
                                            ("llms.txt", "llms.txt"), ("data", "data/site.json")):
                            self.assertIn(f'<li><a href="{root}{href}">{label}</a></li>', f)
            self.assertIn(f'questions go to <a href="{web}/issues">its issues</a>', files["about.html"].decode("utf-8"))
        own = build.repo_web(self.config.get("repo_url"))
        if own:                                             # the public tree
            public(self.files, own, "this tree's")
        else:
            for path, data in sorted(self.files.items()):
                if path.endswith(".html"):
                    with self.subTest(page=path):
                        f = foot(data.decode("utf-8"))
                        root = build.root_of(path)
                        self.assertTrue(f.startswith("<li>Apache-2.0</li>"), f[:80])
                        for label, href in (("How it is scored", "rules.html#courses"), ("Roadmap", "roadmap.html"),
                                            ("Reproduce a score", "reproduce.html"),
                                            ("llms.txt", "llms.txt"), ("data", "data/site.json")):
                            self.assertIn(f'<li><a href="{root}{href}">{label}</a></li>', f)
                        self.assertNotIn("/issues", f)
                        self.assertNotIn(">Source<", f)
        about = norm(text_of(self.files["about.html"]))
        self.assertIn("svGolf is a public proof-golf board for hardware", about)
        self.assertIn("questions go to its issues, and How to submit on each task says how a record is made.", about)
        config = build.load_config()
        config["repo_url"] = "https://example.org/someone/svgolf.git"
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            site = build.build_site(offline=True, config=config)
        public(site.files, "https://example.org/someone/svgolf", "public")

    def test_matmul_says_before_design_that_signed_is_refused(self):
        """Decided 2026-11-11 (the trial runs' finding: `$signed` was refused only at the `design` stage, after
        score/ppa.py had weighed the design): matmul's "Before you design", the visible lead of Proving a new design,
        says it in one sentence, with the hand-written sign extension; the README's bullet stays in the fold."""
        h = self.files["tasks/matmul/index.html"].decode("utf-8")
        part = section(h, "new-design")
        lead = norm(text_of(part[:part.index('<details class="nd-detail"')]))
        self.assertIn("Write no $signed(...) in a wider sum: ls-sv refuses its width conversion at the design stage, "
                      "although score/ppa.py weighs the design; sign-extend a W-bit entry x by hand, "
                      "{{AccW{x[W-1]}}, x}, as the reference does.", lead)
        self.assertIn("no $signed(...) widened into a wider sum", norm(text_of(part)))

    def test_the_score_is_defined_once(self):
        """2026-11-09 (review M2): the Score card is the page's one definition of the score (generated from the task's
        kind: what the time is, the flip-flops in a clocked area), since 2026-11-11 in its closed note "What the score,
        Par, Record and Under par mean"; the task text names the score and links the card rather than define it
        again (and so did "How to participate" step 4, gone since 2026-11-11)."""
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                caption = norm(text_of(section(html_, "score")))
                self.assertIn("Score = area × time: the sky130 cell area of the scored netlist", caption)
                self.assertIn("It is the one ranked number", caption)
                # 2026-11-11: the page head's numbers are defined there too (the quick start's terms, dropped with it)
                self.assertIn("It is the one ranked number: Par (the score of the task's par design, the simplest "
                              "algorithm: the bar to beat), Record (the best accepted score so far, par while no "
                              "submission beats it), Under par (how far the record is below par, as a share of par's "
                              "score) and the leaderboard use it. The Pareto front, area in GE (NAND2 gate equivalents),",
                              caption)
                # one definition: the note, once per course; How to submit and the card do not define it. Each course
                # ranks on its own score (2026-11-12: the routed course ranks), so "the one ranked number" is the
                # sky130 note's words and "this course's ranked number" the routed one's.
                a7 = 'class="pdk-asap7pnr' in html_
                self.assertEqual(text_of(html_).count("It is the one ranked number"), 1)
                self.assertEqual(text_of(html_).count("It is this course's ranked number: Par (the score of the task's "
                                                      "par design"), 1 if a7 else 0)
                if a7:
                    self.assertIn("Score = area × time on ASAP7 placed and routed: the ASAP7 cell area of the design's "
                                  "netlist after place and route", norm(text_of(html_)))
                    self.assertIn("with the wires extracted from the layout", norm(text_of(html_)))
                for sid in ("submit", "new-design"):
                    if f'id="{sid}"' in html_:
                        part = norm(text_of(section(html_, sid)))
                        for again in ("Score = area", "the one ranked number", "this course's ranked number",
                                      "the bar to beat", "gate equivalents"):
                            self.assertNotIn(again, part)
                text = norm(text_of(section(html_, "statement")))
                self.assertNotIn("The score is the", text)
                if build.metrics.is_clocked(json.loads(read_text_file(f"tasks/{t}/task.json"))):
                    self.assertIn('href="#score"', section(html_, "statement"))

    def test_what_does_not_count_is_a_tab_of_the_statement(self):
        """2026-11-09: "What does not count" is the last tab of the statement's tab widget (before, a card at the
        bottom of the page), with the number of rejected designs on the tab and the stage groups inside; the
        statement's intro (and since 2026-11-11 How to submit's Done paragraph) links to it, and the panel's head no longer repeats the number as a counter. Without
        JavaScript the panes stand one under the other, each under its title. 2026-11-11: the panel is in the
        statement's one closed fold, whose summary counts the rejected designs too."""
        for t in self.listed + ["_example"]:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                self.assertNotRegex(html_, r'<section\b[^>]*\bid="does-not-count"')
                spec = section(html_, "spec")
                pane = re.search(r'<div class="props-pane" id="does-not-count"><h4 class="props-pane-title">'
                                 r'What does not count</h4>', spec)
                self.assertTrue(pane, "no pane")
                n = section(html_, "does-not-count").count('<p class="reject-head">')
                tabs = re.findall(r'<a href="#([^"]+)"(?: class="on")? aria-label="([^"]+) \((\d+)\)">\2'
                                  r'<span class="props-n">\3</span></a>', spec.split("</nav>", 1)[0])
                self.assertEqual(tabs[-1], ("does-not-count", "What does not count", str(n)))
                self.assertNotIn("Attacks rejected", html_)
                for sid in ("spec",):
                    self.assertIn('href="#does-not-count"', section(html_, sid))
                # 2026-11-11: How to submit's Done paragraph links it (examples of what step 3 refuses)
                self.assertIn('href="#does-not-count"', section(html_, "submit"))
                fold = spec[spec.index(f'<details class="spec-fold" id="{build.SPEC_FOLD}">'):]
                self.assertIn('<div class="props-pane" id="does-not-count">', fold)
                self.assertIn(f"what does not count ({n})", text_of(fold.split("</summary>", 1)[0]))
                if n:
                    for gid, _, _ in build.REJECT_GROUPS:
                        if f'href="#reject-{gid}"' in html_:
                            self.assertIn(f'<h5 id="reject-{gid}">', section(html_, "does-not-count"))

    def test_llms_txt_carries_the_contract_and_llms_full_the_guide(self):
        llms = self.files["llms.txt"].decode("utf-8")
        for phrase in ("## Step 0", "lake build", "--fetch-liberty", "--no-mapped", "check.py tasks/add solution.sv "
                       "--unproved", "check.py tasks/add solution.sv Solution.lean", "leaderboard.py add",
                       "import Submission.Design", "theorem solution : Goal", "area x time", "llms-full.txt"):
            self.assertIn(phrase, llms)
        # check.py refuses an --unproved run of a latency kind without --latency: llms.txt says so, in the
        # commands and on each such task's line
        latency = [t for t in self.listed
                   if json.loads(read_text_file(f"tasks/{t}/task.json")).get("kind") in build.LATENCY_KINDS]
        self.assertEqual("--unproved needs --latency n" in llms, bool(latency))
        for t in latency:
            with self.subTest(task=t):
                line = next(ln for ln in llms.split("\n") if ln.startswith("- [") and f"(`{t}`)" in ln)
                self.assertIn("`check.py --unproved` needs `--latency n` on it (par's n: ", line)
        full = self.files["llms-full.txt"].decode("utf-8")
        self.assertIn("## 0. The loop", full)
        self.assertIn("sv_structure?", full)

    def test_llms_txt_points_to_the_library_tables(self):
        """2026-11-13 (provers re-proved and copied lemmas the libraries have): PROVING.md's section 6 is the tables
        of library lemmas by area, llms.txt links it by its heading's anchor, the anchor is on proving.html, and every
        task README that points to section 6 uses that anchor."""
        proving = read_text_file("PROVING.md")
        head = re.search(rf"^## ({build.LIBRARY_SECTION_NO}\. .+)$", proving, re.M).group(1)
        self.assertEqual(head, "6. What the libraries already give you")
        anchor = build.md.Slugger().slug(head)
        self.assertIn(f"- [What the libraries already give you, by area](proving.html#{anchor})",
                      self.files["llms.txt"].decode("utf-8"))
        self.assertIn(f'id="{anchor}"', self.files["proving.html"].decode("utf-8"))
        self.assertIn("### Common friction (2026-11-13)", proving)
        for t in sorted(os.listdir(os.path.join(SVGOLF, "tasks"))):
            if os.path.isfile(os.path.join(SVGOLF, "tasks", t, "README.md")):
                with self.subTest(task=t):
                    readme = read_text_file(f"tasks/{t}/README.md")
                    for target in re.findall(r"\(\.\./\.\./PROVING\.md#(6-[\w-]+)\)", readme):
                        self.assertEqual(target, anchor)
                    self.assertNotIn("a task ships no library: copy", readme)

    def test_llms_txt_points_to_the_numbers_of_a_task_page(self):
        """llms.txt (2026-11-11) names where par, record and under par, the clock period and the score chart are
        defined (the rules page's section, which exists), and says that the sky130 score counts no wires and no place
        and route while the second course, ASAP7 placed and routed, does (2026-11-12), with where its rules are."""
        llms = self.files["llms.txt"].decode("utf-8")
        self.assertIn("\nPar, record and under par, the clock period and the score chart: "
                      "rules.html#task-page-numbers.\n", llms)
        self.assertIn('id="task-page-numbers"', self.files["rules.html"].decode("utf-8"))
        self.assertIn("sky130 is the default course, and its score counts the cells only: no wires, no place and route.",
                      llms)
        self.assertIn("The second course is ASAP7 placed and routed: each design's ASAP7 netlist placed and routed by "
                      "OpenROAD-flow-scripts, one run per design, the wires extracted from the layout", llms)
        self.assertIn(f"rules.html#{build.ASAP7PNR_ANCHOR}", llms)
        self.assertIn(f'id="{build.ASAP7PNR_ANCHOR}"', self.files["rules.html"].decode("utf-8"))

    def test_the_general_pages_know_a_clocked_task(self):
        """Once a clocked task is listed (the arbiter, 2026-11-07), no general page says every task is
        combinational, and llms.txt says how a clocked task is weighed and what its time is."""
        clocked = [t for t in self.listed if build.metrics.is_clocked(json.loads(read_text_file(f"tasks/{t}/task.json")))]
        if not clocked:
            self.skipTest("no clocked task is listed")
        llms = self.files["llms.txt"].decode("utf-8")
        texts = {p: text_of(self.files[p].decode("utf-8")) for p in ("index.html", "about.html", "roadmap.html")}
        texts["llms.txt"] = llms
        for p, text in texts.items():
            for stale in ("Every task is combinational", "write a combinational circuit", "clocked processes are refused"):
                with self.subTest(page=p, stale=stale):
                    self.assertNotIn(stale, text)
        self.assertIn("(combinational, or clocked on a clocked task such as", llms)
        for t in clocked:
            line = next(ln for ln in llms.split("\n") if f"(`{t}`)" in ln)
            self.assertIn("Clocked: weigh it with `score/ppa.py --seq`; its time is the register-to-register clock "
                          "period", line)
        self.assertIn("on a clocked task, keeps the task's property on every cycle", texts["about.html"])

    def test_task_texts_type_no_measured_number(self):
        """content/tasks/<t>.md fills its numbers from the data (placeholders): none is typed by hand,
        and none is left unfilled on the page."""
        for t in self.listed:
            with self.subTest(task=t):
                src = read_text_file(f"site/content/tasks/{t}.md")
                self.assertEqual([m.group(0) for m in build.HAND_TYPED.finditer(build.PLACEHOLDER.sub("", src))], [])
                statement = section(self.files[f"tasks/{t}/index.html"].decode("utf-8"), "statement")
                self.assertNotIn("{{", statement)
                # 2026-11-11: the text's first GE says what GE is, once
                ge = [m for m in build.PLACEHOLDER.finditer(src) if m.group(2) == "ge"]
                self.assertEqual(text_of(statement).count(f"GE ({build.GE_GLOSS})"), 1 if ge else 0)

    def test_home_hero_holds_the_buttons_and_its_art_is_decoration(self):
        """The hero's drawing (pixelart.py) is aria-hidden SVG with no text; the buttons sit in the hero under
        the lead, and the home page has no strip of counts (decided 2026-11-06)."""
        html_ = self.files["index.html"].decode("utf-8")
        start = html_.index('<header class="hero')
        hero = html_[start:html_.index("</header>", start)]
        svgs = re.findall(r"<svg\b[^>]*>.*?</svg>", hero, re.S)
        self.assertEqual(len(svgs), 1)                     # the scene
        self.assertIn('aria-hidden="true"', svgs[0])
        self.assertEqual(text_of(svgs[0]), "")
        self.assertIn(self.config["headline"]["title"], text_of(hero))          # config.json's (2026-11-11)
        self.assertLess(hero.index('class="hero-lead"'), hero.index('class="btn-row"'))
        for button in ("Start with the tutorial", "Read the rules", "The proving guide"):
            self.assertIn(button, text_of(hero))
        between = html_[html_.index("</header>", start):html_.index('<ul class="task-cards">')]
        self.assertNotIn('class="stats', between)          # the cards' own par and record are the only numbers

    def test_the_tutorial_is_shown_as_a_tutorial(self):
        """2026-11-12, display only: the tutorial's page is headed "Tutorial: <title>" (its first word in lower case),
        with no task-id chip and no number; its crumbs say "tutorial"; its <title>, link preview and description name
        it as a tutorial; no badge repeats the word; its home card has "start here" in the number's box, where a listed
        task has its number, and the page's title, without the slug (decided 2026-11-12), and no "00" is left; its
        record, reference and properties pages name it "tutorial" in their crumbs, titles, h1 and descriptions
        (decided 2026-11-12). The slug stays: the page's path and the commands keep `_example`. Every other task
        keeps its h1 with the chip, its number and its crumbs."""
        self.assertEqual(build.tutorial_title("Bitwise AND"), "Tutorial: bitwise AND")
        self.assertEqual(build.tutorial_title("AES S-box"), "Tutorial: AES S-box")       # an acronym stays
        self.assertEqual(build.tutorial_title("Adder"), "Tutorial: adder")
        tut = [t for t, how in self.config["tasks"].items() if how == "tutorial"]
        self.assertEqual(tut, ["_example"])
        with open(os.path.join(SITE, "content", "tasks", "_example.json"), encoding="utf-8") as fh:
            title = json.load(fh)["title"]
        want = build.tutorial_title(title)
        self.assertEqual(want, "Tutorial: bitwise AND")
        page_ = self.files["tasks/_example/index.html"].decode("utf-8")
        start = page_.index('<p class="crumbs">')
        head = page_[start:page_.index("</header>", start)]
        self.assertEqual(re.search(r"<h1>(.*?)</h1>", head, re.S).group(1), html.escape(want))
        self.assertNotIn('class="task-id"', head)
        self.assertNotIn('class="task-no"', head)
        crumbs = re.search(r'<p class="crumbs">(.*?)</p>', head, re.S).group(1)
        self.assertEqual(norm(text_of(crumbs)), "‹Tasks / tutorial")
        self.assertNotIn("badge-tutorial", page_)
        self.assertIn(f"<title>{html.escape(want, quote=False)} | svGolf</title>", page_)
        meta = {a.get("property") or a.get("name"): a.get("content")
                for tag, a in self.pages["tasks/_example/index.html"].tags if tag == "meta"}
        self.assertEqual(meta["og:title"], f"{want} | svGolf")
        self.assertTrue(meta["description"].startswith("svGolf tutorial: bitwise AND. "), meta["description"])
        self.assertNotIn("_example", meta["description"])
        self.assertIn("tasks/_example/index.html", self.files)          # the slug stays
        self.assertIn("cp tasks/_example/reference/", text_of(page_))
        for t, how in self.config["tasks"].items():
            if how in ("listed", "preview"):
                with self.subTest(task=t):
                    other = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                    self.assertRegex(other, r'<span class="task-no" aria-hidden="true">\d\d</span><h1>[^<]* <span '
                                            rf'class="task-id"><code>{re.escape(t)}</code></span></h1>')
                    self.assertIn(f"</span>Tasks</a> / {t}</p>", other)
        home = self.files["index.html"].decode("utf-8")
        cards = re.findall(r'<li class="task-card"><div class="task-card-top">(.*?)</div>', home, re.S)
        self.assertTrue(cards[0].startswith('<span class="task-no"><span class="label label-accent task-start">'
                                            'start here</span></span>'), cards[0])
        self.assertNotIn("_example", cards[0])                       # no slug on the card
        first = home.split('<li class="task-card">', 2)[1]
        self.assertEqual(norm(text_of(re.search(r"<h3>(.*?)</h3>", first, re.S).group(1))), want)
        marks = [re.match(r'<span class="([^"]+)">([^<]*)</span>', c).groups() for c in cards[1:]]
        self.assertEqual([m for m in marks if m[0] != "task-no"], [])
        self.assertEqual([m[1] for m in marks], [f"{k:02d}" for k in range(1, len(cards))])
        self.assertNotIn('<span class="task-no">00</span>', home)
        # its other pages: "tutorial" in the crumbs, the <title>, the h1 and the description
        others = sorted(p for p in self.files if p.startswith("tasks/_example/") and p.endswith(".html")
                        and p != "tasks/_example/index.html")
        self.assertTrue(any("/records/" in p for p in others) and any("/reference/" in p for p in others), others)
        for rel in others:
            with self.subTest(page=rel):
                h = self.files[rel].decode("utf-8")
                crumbs = norm(text_of(re.search(r'<p class="crumbs">(.*?)</p>', h, re.S).group(1)))
                self.assertTrue(crumbs.startswith("‹Tasks / tutorial / "), crumbs)
                title = html.unescape(re.search(r"<title>(.*?)</title>", h).group(1))
                h1 = norm(text_of(re.search(r"<h1>(.*?)</h1>", h, re.S).group(1)))
                meta = {a.get("property") or a.get("name"): a.get("content") for tag, a in self.pages[rel].tags
                        if tag == "meta"}
                for said in (title, h1, meta["description"]):
                    self.assertNotIn("_example", said)
                self.assertIn("tutorial", title)
                self.assertTrue(meta["description"].startswith("svGolf tutorial: "), meta["description"])
                if "/records/" in rel:
                    self.assertRegex(title, r" on the tutorial · record [0-9a-f]{12} \| svGolf$")
                    # the heading is the record's title since 2026-11-13; who, where and when is the line under it
                    sub = norm(text_of(re.search(r'<p class="head-sub">(.*?)</p>', h, re.S).group(1)))
                    self.assertIn(" on the tutorial · ", sub)

    def test_the_headline_has_one_source(self):
        """Decided 2026-11-11: the front page's headline and its sub-line are config.json `headline`, and everything
        that says it follows: the front page's h1 (its end on the highlighter), sub-line, <title> and description,
        every page's footer line, llms.txt's summary; README.md's first line repeats it (compared here); home.md has
        no title of its own, and the former headline and the placeholder before the pick are nowhere."""
        hl, lib = self.config["headline"], self.config["library"]
        title, accent = hl["title"], hl["accent"]
        sub_text = hl["sub"].replace("{library}", lib["name"])
        home = self.files["index.html"].decode("utf-8")
        h1 = re.search(r"<h1>(.*?)</h1>", home, re.S).group(1)
        self.assertEqual(text_of(h1), title)
        self.assertTrue(title.endswith(accent))
        self.assertIn(f'<span class="accent">{html.escape(accent, quote=False)}</span></h1>', home)
        sub = re.search(r'<div class="hero-lead"><p class="hero-sub">(.*?)</p>', home, re.S).group(1)
        self.assertEqual(text_of(sub), sub_text)
        self.assertIn(f'<a href="{lib["url"]}">{lib["name"]}</a>', sub)
        self.assertIn(f"<title>{html.escape('svGolf: ' + title.rstrip('.'), quote=False)}</title>", home)
        description = re.search(r'<meta name="description" content="([^"]*)">', home).group(1)
        self.assertEqual(html.unescape(description), f"svGolf: {title[0].lower()}{title[1:]} {sub_text}")
        for path, data in sorted(self.files.items()):
            if path.endswith(".html"):
                with self.subTest(page=path):
                    foot = data.decode("utf-8").split('<div class="foot-brand">', 1)[1].split("</div>", 1)[0]
                    self.assertTrue(text_of(foot).endswith("svGolf" + title), text_of(foot)[-120:])
                    self.assertNotIn("golf its gates", data.decode("utf-8"))
                    self.assertNotIn("smallest, fastest circuit you can prove", data.decode("utf-8"))
        llms = self.files["llms.txt"].decode("utf-8").split("\n")
        self.assertEqual(llms[:2], ["# svGolf", ""])
        self.assertTrue(llms[2].startswith(f"> {title} "), llms[2][:120])
        readme = read_text_file("README.md").split("\n\n")
        self.assertEqual(readme[0], "# svGolf")
        self.assertEqual(" ".join(readme[1].split()),
                         f"**{title}** " + hl["sub"].replace("{library}", f"[{lib['name']}]({lib['url']})"))
        self.assertFalse(re.search(r"^# ", read_text_file("site/content/home.md"), re.M))

    def test_the_library_is_named_and_linked_from_one_config_value(self):
        """Decided 2026-11-11: the Lean library the proofs are written with is named and linked where the site says what a
        proof is made with: the front page's sub-line, About's paragraph on it, How to submit's Lean file (under the
        generated module, whose `LeanModels.*` import is its), the proving guide's opening, every page's footer,
        llms.txt and README's first screen. Its name comes from config.json `library` alone: the site's code and its
        content files do not write it out."""
        lib = self.config["library"]
        name, url = lib["name"], lib["url"]
        link = f'<a href="{url}">{name}</a>'
        home = self.files["index.html"].decode("utf-8")
        self.assertIn(link, re.search(r'<p class="hero-sub">(.*?)</p>', home, re.S).group(1))
        about = self.files["about.html"].decode("utf-8")
        para = next(p for p in re.findall(r"<p>(.*?)</p>", about, re.S) if link in p)
        self.assertIn("a Lean 4 library for proving real programs correct", norm(text_of(para)))
        self.assertIn("It also covers Python and C++.", norm(text_of(para)))
        for t in self.listed:
            with self.subTest(task=t):
                submit = section(self.files[f"tasks/{t}/index.html"].decode("utf-8"), "submit")
                generated = submit.index("Submission.Design (generated: you never write it)")
                said = submit.index(f"<p>The <code>LeanModels.*</code> modules are {link}'s, the library of ls-sv and "
                                    "its tactics.</p>")
                self.assertLess(generated, said)
        proving = self.files["proving.html"].decode("utf-8")
        first = re.search(r'<article class="card doc-body">\s*<p>(.*?)</p>', proving, re.S).group(1)
        self.assertIn(link, first)
        for path, data in sorted(self.files.items()):
            if path.endswith(".html"):
                with self.subTest(page=path):
                    foot = data.decode("utf-8").split('<ul class="foot-links">', 1)[1].split("</ul>", 1)[0]
                    self.assertIn(f"<li>Lean library: {link}</li>", foot)
        self.assertIn(f"prove in Lean 4 with {name} ({url}) that it meets", self.files["llms.txt"].decode("utf-8"))
        readme_top = "\n".join(read_text_file("README.md").split("\n")[:40])
        self.assertIn(f"[{name}]({url})", readme_top)
        self.assertNotIn("[proglib](", readme_top)                  # the prose writes the display name
        self.assertIn(f"[{name}]({url})", read_text_file("PROVING.md").split("\n\n")[1])
        for src in ("site/build.py", "site/page.py", "site/content/about.md", "site/content/home.md"):
            self.assertNotIn(name, read_text_file(src), src)

    def test_the_readme_is_a_front_door_and_the_docs_name_the_library(self):
        """README above its Quick start (decided 2026-11-12): the site, the clone command, the platforms (the rating
        build; Windows not supported) and a where-to-go table of five rows, with the ls-sv tier names moved into "The
        statement". One suite-time figure in README and CONTRIBUTING, whose step list is tests/run.py's STEPS and whose
        no-Lean selection skips every other step. The docs write the library's display name in prose; the generated
        install texts, the record pages, the rules page and the front page take it from config.json."""
        lib = self.config["library"]
        name, link = lib["name"], f'<a href="{lib["url"]}">{lib["name"]}</a>'
        readme = read_text_file("README.md")
        top = readme.split("\n## Quick start\n", 1)[0]
        self.assertIn("<https://thomasnormal.github.io/svgolf/>", top)
        self.assertIn("```bash\ngit clone https://github.com/thomasnormal/svgolf\n```", top)
        self.assertIn("macOS and Linux; Windows is not supported. The ranked numbers are made by one build, the "
                      "WebAssembly Yosys 0.53 that pip install -r requirements.txt installs", norm(top))
        table = top.split("| where | what |\n|---|---|\n", 1)[1].split("\n\n", 1)[0].split("\n")
        self.assertEqual([re.match(r"\| \[?`?([^`\]|]+)", row).group(1) for row in table],
                         ["the site", "tasks/<name>/README.md", "PROVING.md", "CONTRIBUTING.md", "REFUSALS.md"])
        self.assertNotIn("Terminates2", top)
        statement = readme.split("\n## The statement\n", 1)[1].split("\n## ", 1)[0]
        self.assertIn("tier of Proglib's ls-sv semantics: load_design_sv2, run2, the ⊨₂ judgment and Terminates2", norm(statement))
        contrib = read_text_file("CONTRIBUTING.md")
        for doc, text in (("README.md", readme), ("CONTRIBUTING.md", contrib)):
            with self.subTest(doc=doc):
                self.assertIn("the whole suite takes an hour or more on a laptop", norm(text).lower())
                for stale in ("226 checks", "386 checks", "3154 s", "44 checks", "PLAN2.md):"):
                    self.assertNotIn(stale, text)
        # (a step's name may have a hyphen: `baseline-proofs`, 2026-11-12)
        steps = re.findall(r'"([\w-]+)"', re.search(r"^STEPS = \[(.*?)\]", read_text_file("tests/run.py"),
                                                    re.S | re.M).group(1))
        self.assertIn("baseline-proofs", steps)
        self.assertEqual(re.findall(r"`([\w-]+)`", re.search(r"Steps: (.*?)\.", " ".join(contrib.split())).group(1)), steps)
        skipped = re.search(r"--skip (\S+) +# no Lean", contrib).group(1).split(",")
        self.assertEqual(sorted(skipped + ["canon", "layout", "leaderboard", "unit"]), sorted(steps))
        task_readmes = sorted(f"tasks/{t}/README.md" for t in os.listdir(os.path.join(SVGOLF, "tasks"))
                              if os.path.isfile(os.path.join(SVGOLF, "tasks", t, "README.md")))
        self.assertIn("tasks/arbiter/README.md", task_readmes)
        for rel in ("README.md", "PROVING.md", "CONTRIBUTING.md", "leaderboard/README.md", *task_readmes):
            with self.subTest(doc=rel):     # the repository and command names stay lowercase: proglib, proglib-run
                self.assertEqual(re.findall(r"(?<![/\w.-])proglib(?![-\w/.])", read_text_file(rel)), [])
        llms = self.files["llms.txt"].decode("utf-8")
        self.assertIn(f"Lake clones {name} (formerly lean-surfaces) and its packages", llms)
        for t in self.listed:
            with self.subTest(task=t):
                self.assertIn("about 20 minutes, plus 8 for elan&#x27;s first download of the toolchain, on a slower "
                              "Linux machine", self.files[f"tasks/{t}/index.html"].decode("utf-8"))   # Step 0
        pages = [p for p in self.files if "/records/" in p and p.endswith(".html")]
        self.assertTrue(pages)
        for p in pages:
            text = text_of(self.files[p])
            self.assertIn(f"{name} revision", text, p)
            self.assertNotIn("lean-surfaces revision", text, p)
        rules = text_of(self.files["rules.html"])          # the stage table names the library by its name (2026-11-13)
        self.assertIn(f"The table is the text of the refusal register of {name}.", rules)
        self.assertNotIn("by its former name", rules)
        self.assertIn(f"the pinned extractor of {link} (formerly lean-surfaces)", self.files["index.html"].decode("utf-8"))

    def test_the_hand_off_is_said_in_the_same_words(self):
        """How a record reaches the board, in one sentence (decided 2026-11-11; build.py HANDOFF_MD): README (its Quick
        start and its Leaderboard, so the rules page too), CONTRIBUTING and leaderboard/README.md say it word for word,
        and About writes `{{handoff}}`; none of them says that the route is an open decision or a possible hand-off,
        that there is no submission server YET, or that CI re-verifies a record. README's Leaderboard says who added
        the records so far."""
        want = norm(build.HANDOFF_MD)
        for rel in ("README.md", "CONTRIBUTING.md", "leaderboard/README.md"):
            with self.subTest(doc=rel):
                text = read_text_file(rel)
                self.assertIn(want, norm(text))
                for stale in ("open decision", "possible hand-off", "CI re-verifies", "no submission server yet"):
                    self.assertNotIn(stale, text.lower() if stale != "CI re-verifies" else text)
        self.assertEqual(norm(read_text_file("README.md")).count(want), 2)            # Quick start and Leaderboard
        self.assertIn("{{handoff}}", read_text_file("site/content/about.md"))
        rules = text_of(self.files["rules.html"])
        self.assertIn(want, norm(rules))
        for stale in ("open decision", "possible hand-off", "CI re-verifies"):
            self.assertNotIn(stale, rules)
        first = norm(build.FIRST_ENTRIES_MD)                    # README's Leaderboard words (test_the_claims_...)
        # decided 2026-11-13: the maintainers' records are entries like any, seeded with AI assistance; since the first
        # outside records (2026-11-24) the line says how outside entries come in
        self.assertEqual(first, "The board is seeded with entries the maintainers made with AI assistance (each record "
                         "names the tools), each proved and scored like any entry: they are ordinary entries and can "
                         "be beaten. Outside entries come in by pull request; the first came on 2026-11-24.")
        self.assertNotIn("trial design", norm(text_of(self.files["index.html"])))
        self.assertIn(first, norm(read_text_file("README.md")))
        self.assertIn(first, norm(rules))
        # what holds for every record, whoever made it (decided 2026-11-12: an unassisted outside record is valid and
        # must not turn this test red): `assisted_by` is a list of names, and the record's page says them, or that the
        # record claims no help. The line above is the maintainers' to change with the first outside record
        # (CONTRIBUTING.md, "For the maintainers").
        for r in records():
            with self.subTest(record=r["record_hash"][:12]):
                self.assertIsInstance(r["assisted_by"], list)
                self.assertTrue(all(isinstance(a, str) and a for a in r["assisted_by"]))
                page_ = self.files[f"tasks/{r['task']}/records/{r['record_hash']}.html"].decode("utf-8")
                # (since 2026-11-23 the record hashes it names are links: test_writeups_and_notes_link_...)
                said = re.search(r"<dt>assisted by</dt><dd>(.*?)</dd>", page_, re.S).group(1)
                self.assertEqual(player_words(said), "; ".join(r["assisted_by"]) or "none (an unassisted claim)")

    def test_roadmap_is_off_the_nav_and_linked_from_about(self):
        """The nav has no Roadmap (decided 2026-11-06); roadmap.html is still built and About links it."""
        nav = re.search(r'<nav class="site-nav"[^>]*>(.*?)</nav>', self.files["index.html"].decode("utf-8"), re.S)
        self.assertNotIn("roadmap.html", nav.group(1))
        self.assertIn("roadmap.html", self.files)
        self.assertIn('href="roadmap.html"', self.files["about.html"].decode("utf-8"))

    def test_the_trust_page_says_what_is_proved_trusted_measured_and_sampled(self):
        """Decided 2026-11-17: the one page on what a record proves and trusts (trusted/index.html), made exact and
        complete, and linked from every page's footer. It says what is proved (each task's statement and every
        condition of its range, task.json's, which agrees with the statement's own `inRange`), what is trusted (the
        Lean kernel with the comparator, the statements, the SystemVerilog front end from the parser to the generated
        module, the source gate, and for the score only the synthesis and timing flow), what is only measured and what
        is only a sanity check, each part naming files that exist. No page says "Nothing else is trusted", and no
        task's text claims a range its statement does not have (generated: `{{range}}`)."""
        h = self.files["trusted/index.html"].decode("utf-8")
        ids = [build.TRUST_PROVED, build.TRUST_TRUSTED, build.TRUST_MEASURED, build.TRUST_SAMPLED, build.TRUST_MODULES]
        at = [h.index(f'id="{i}"') for i in ids]
        self.assertEqual(at, sorted(at))
        self.assertIn(f"<h1>{build.TRUST_TITLE}</h1>", h)
        proved = norm(text_of(section(h, build.TRUST_PROVED)))
        for t in self.ranked:
            task = json.loads(read_text_file(f"tasks/{t}/task.json"))
            with self.subTest(task=t):
                self.assertIn(task["statement"]["constant"], proved)
                params = task.get("parameters") or []
                for p in params:
                    for cond in p["range"].split(", "):
                        self.assertIn(cond, proved)
                # the range is the statement's: every power of two in task.json's bounds is one of inRange's
                spec = read_text_file(f"tasks/{t}/Spec.lean")
                defs = " ".join(ln for ln in spec.split("\n") if re.search(r"\binRange\b.*:=", ln)
                                and not ln.lstrip().startswith("example"))
                self.assertEqual(sorted(set(re.findall(r"2\^(\d+)", " ".join(p["range"] for p in params)))),
                                 sorted(set(re.findall(r"2 \^ (\d+)", defs))), defs)
                # and so is every other number in them (matmul's `N <= 256` since 2026-11-19): the numbers of the
                # lines that define inRange, without the powers of two and the pairs' projections (`p.2.1`)
                def numbers(s, power):
                    s = re.sub(power, " ", s)
                    return {int(x) for x in re.findall(r"(?<![\w.])\d+(?![\w.])", s)} - {0}
                own = " ".join(ln for ln in spec.split("\n") if re.match(r"\s*(def\s+)?inRange\b.*:=", ln))
                self.assertEqual(numbers(" ".join(p["range"] for p in params), r"2\^\d+"),
                                 numbers(own, r"2 \^ \d+"), own)
                statement = norm(text_of(section(self.files[f"tasks/{t}/index.html"].decode("utf-8"), "statement")))
                self.assertNotRegex(statement, r"every (width )?N ≥ 1")
                for p in params:
                    for cond in p["range"].split(", "):
                        self.assertIn(cond, statement)
                self.assertNotIn("{{range}}", statement)
        trusted = norm(text_of(section(h, build.TRUST_TRUSTED)))
        for part in ("The Lean kernel.", "The statements.", "The SystemVerilog front end.", "The source gate.",
                     "For the score only, the synthesis and timing flow."):
            self.assertIn(part, trusted)
        named = ["check/Comparator.lean", "check.py", "check/envelope.py", "score/srcgate.py", "score/canon.ys",
                 "score/svgolf.ys", "score/svgolf_seq.ys", "score/ppa.py", "score/ppa_pins.json"]
        for rel in named:
            self.assertIn(rel, trusted)
            self.assertTrue(os.path.isfile(os.path.join(SVGOLF, *rel.split("/"))), rel)
        for said in ("load_design_sv2", "LeanModels.Sv.Ingest2", "extractors/sv/extract.py", "Submission.Design",
                     "propext", "leanchecker", "never what its proof says"):
            self.assertIn(said, trusted)
        with open(os.path.join(SVGOLF, "requirements.txt"), encoding="utf-8") as fh:
            pin = next(ln.strip() for ln in fh if ln.strip() and not ln.startswith("#"))
        self.assertIn(pin, trusted)
        self.assertIn("not proved", norm(text_of(section(h, build.TRUST_MEASURED))))
        sampled = norm(text_of(section(h, build.TRUST_SAMPLED)))
        for rel in ("check/postsynth.py", "score/fourstate.py"):
            self.assertIn(rel, sampled)
            self.assertTrue(os.path.isfile(os.path.join(SVGOLF, *rel.split("/"))), rel)
        self.assertIn("That is sampling, not a proof.", sampled)
        for path, data in self.files.items():
            if not path.endswith(".html"):
                continue
            with self.subTest(page=path):
                self.assertNotIn("nothing else is trusted", text_of(data).lower())
                foot = data.decode("utf-8").split('<footer class="site-footer">', 1)[1]
                self.assertIn(f'<a href="{build.root_of(path)}trusted/index.html">{build.TRUST_FOOT}</a>', foot)
        home = norm(text_of(self.files["index.html"]))
        self.assertIn("for every N with 1 <= N < 2^20, whenever the inputs are known", home)

    def test_try_it_without_lean_under_the_tasks(self):
        """Decided 2026-11-17, moved 2026-11-20: the tasks come right under the front page's hero, and under the task
        cards, "Try it without Lean": the exact commands that score
        a design with the real tools on your own machine (the virtual environment, pyslang, the liberty, then
        score/ppa.py on the adder's par design), where to get the pinned Yosys (Step 0's recipe on the tutorial, which
        the link opens), the line score/ppa.py prints last for it (README's Quick start quotes it, from a real run),
        and one plain sentence that a record needs a proof. home.md's own steps point to it rather than repeat it."""
        home = self.files["index.html"].decode("utf-8")
        hero_end = home.index("</header>", home.index('<header class="hero'))
        self.assertTrue(home[hero_end:].startswith('</header>\n<section class="course">'),
                        home[hero_end:hero_end + 120])
        box = section(home, "try-it-without-lean")
        cards_end = home.index("</section>", home.index('<section class="course">'))
        self.assertTrue(home[cards_end:].startswith('</section>\n<section class="card try" id="try-it-without-lean">'),
                        home[cards_end:cards_end + 120])
        block = html.unescape(re.sub(r"<[^>]+>", "", re.search(r"<pre\b[^>]*>(.*?)</pre>", box, re.S).group(1)))
        cmds = [ln for ln in block.replace(" \\\n    ", " ").split("\n") if ln and not ln.startswith("#")]
        par = lb.par_stem(os.path.join(SVGOLF, "tasks"), lb.load_task(os.path.join(SVGOLF, "tasks"), "add"))
        self.assertEqual(cmds[-4:], ["python3.12 -m venv .venv && . .venv/bin/activate",
                                     "python3.12 -m pip install -r requirements.txt",
                                     "python3.12 score/ppa.py --fetch-liberty",
                                     f"python3.12 score/ppa.py tasks/add/reference/{par}.sv --task tasks/add --no-mapped"])
        # the line ppa.py prints last: README quotes it for the adder's par, from a real run
        quoted = re.search(r"`(ppa \(sky130 A0'\): area [^`]+)` for the adder's par", read_text_file("README.md"))
        self.assertIsNotNone(quoted)
        said = " ".join(ln.lstrip("# ").strip() for ln in block.split("\n") if ln.startswith("# ppa") or
                        ln.startswith("#     area x"))
        self.assertEqual(said, quoted.group(1))
        text = norm(text_of(box))
        self.assertIn("A record on the board also needs a Lean proof that the design meets the task's statement; "
                      "scoring needs none.", text)
        self.assertIn(f'href="tasks/_example/index.html#{build.YOSYS_RECIPE}"', box)
        self.assertIn(f'id="{build.YOSYS_RECIPE}"', self.files["tasks/_example/index.html"].decode("utf-8"))
        self.assertIn('href="#try-it-without-lean"', home[home.index('<section class="how"'):])
        self.assertEqual(norm(text_of(home)).count("score/ppa.py --fetch-liberty"), 1)

    def latest_rows(self, h):
        """The rows of a latest list (latest.html's, or the front page's strip) in `h`, in order: (task, record hash,
        the score cell's number, the line under it, the row's HTML)."""
        out = []
        lists = "".join(re.findall(r'<ol class="latest">(.*?)</ol>', h, re.S))
        for li in re.findall(r"<li\b[^>]*>.*?</li>", lists, re.S):
            m = re.search(r'href="(?:\.\./)*tasks/([^/]+)/records/([0-9a-f]{64})\.html"', li)
            cell = re.search(r'<div class="board-score">(.*)</div></li>', li, re.S).group(1)
            num, _, under = cell.partition("<small>")
            out.append((m.group(1), m.group(2), norm(text_of(num)), norm(text_of(under)), li))
        return out

    def test_latest_order_on_ties(self):
        """`latest_records` on made-up tasks: newest date first; a record that gives a time comes before one of the
        same day that does not, and later times first; then the tutorial, the tasks by number, the player, the hash;
        the same order whatever order the tasks and records come in."""
        def rec(h, date, player="p"):
            return {"record_hash": h, "submitted_at": date, "player": player}
        tut = types.SimpleNamespace(name="_example", listing="tutorial", number=None,
                                    records=[rec("t1", "2026-11-13")])
        a = types.SimpleNamespace(name="add", listing="listed", number="01",
                                  records=[rec("a2", "2026-11-13", "b"), rec("a1", "2026-11-13", "b"),
                                           rec("a0", "2026-11-13", "a"), rec("a3", "2026-11-14")])
        m = types.SimpleNamespace(name="mul", listing="listed", number="02",
                                  records=[rec("m1", "2026-11-13T08:00:00Z"), rec("m2", "2026-11-13T09:30:00Z"),
                                           rec("m0", "2026-11-12")])
        want = ["a3", "m2", "m1", "t1", "a0", "a1", "a2", "m0"]
        for tasks in ([tut, a, m], [m, a, tut]):
            for t in tasks:
                t.records.reverse()
            self.assertEqual([r["record_hash"] for _, r in build.latest_records(tasks)], want)

    def test_a_record_against_the_best_on_made_up_boards(self):
        """Decided 2026-11-25 (the owner: "show how good they are relative to the current best"): `vs_best` on made-up
        boards, ranked as leaderboard.py ranks them (equal scores share a rank). The first place: "best" and how far it
        is ahead of the next place; with no other place "best" alone; equal first places "tied for best". Any other
        place: how far it is behind. Both are shares of the best's score, so the second place's "behind" is the first
        place's "ahead". Only a first place is good news. A share that would round to 0% keeps two significant digits
        (under par's rule, now also at exactly half a percent). Not ranked, or a preview: None."""
        def task(*rows, preview=False):
            ranking = [{"record_hash": h, "rank": k, "exact": e, "player": f"p-{h}"} for h, k, e in rows]
            designs = [{"id": h, "kind": "record", "m": {"adp": e / 100}} for h, _, e in rows]
            return types.SimpleNamespace(board={"ranking": ranking}, designs=designs, preview=preview)

        def said(t, h):
            phrases, good, title = build.vs_best(t, h)
            return " · ".join(phrases), good
        one = task(("a", 1, 1000))
        self.assertEqual(build.vs_best(one, "a"), (("best",), True, "rank 1 of 1 on this course's board"))
        self.assertIsNone(build.vs_best(one, "b"))
        self.assertIsNone(build.vs_best(task(("a", 1, 1000), preview=True), "a"))
        t = task(("a", 1, 1000), ("b", 2, 1250), ("c", 3, 3000))
        phrases, good, title = build.vs_best(t, "a")
        self.assertEqual((phrases, good), (("best", "25% ahead of the next"), True))
        self.assertTrue(title.startswith("rank 1 of 3 on this course's board; the next: p-b, "), title)
        self.assertEqual(said(t, "b"), ("25% behind the best", False))
        self.assertEqual(said(t, "c"), ("200% behind the best", False))
        self.assertIn("rank 3 of 3 on this course's board; the best: p-a, ", build.vs_best(t, "c")[2])
        tied = task(("a", 1, 1000), ("b", 1, 1000), ("c", 3, 1100))
        for h in "ab":
            self.assertEqual(said(tied, h), ("tied for best · 10% ahead of the next", True))
        self.assertEqual(said(tied, "c"), ("10% behind the best", False))
        self.assertEqual(said(task(("a", 1, 7), ("b", 1, 7)), "b"), ("tied for best", True))
        close = task(("a", 1, 100000), ("b", 2, 100035))
        self.assertEqual(said(close, "a")[0], "best · 0.035% ahead of the next")
        self.assertEqual(said(close, "b")[0], "0.035% behind the best")
        self.assertEqual([build.pct_text(x) for x in (0, 0.005, 0.0049, 0.015, 0.68, 3.53)],
                         ["0%", "0.5%", "0.49%", "2%", "68%", "353%"])
        self.assertEqual(build.under_text(0.005), "0.5%")
        self.assertEqual(build.under_text(-0.005), "0.5% over par")
        self.assertEqual(build.under_text(-0.05), "5% over par")

    def test_good_news_is_green(self):
        """Decided 2026-11-25 (the owner: ""13% under par" is a good thing, so it should be green, not red"; on 11-24
        the same of the Under par tile): every figure that says a design is under par, best, ahead or better than par
        or than another design is in the site's good colour, and nothing of the kind is in the accent or the error
        colour. In style.css: the class `good` and the latest list's first place are `--good-ink`, behind and over
        par are neutral text, the record pages' meter of the players a design beats and the board table's first
        place are `--good`; the accent class the latest list used for under par is gone. On the pages: the latest
        list (test_pdk.py, both courses), and a record page's "vs par" rows, its "on this page" first places and its
        Charts tab's "this design vs it" column, green exactly where the design is the better one."""
        css = read_text_file("site/style.css")

        def rule(sel):
            m = re.search(rf"^\s*{re.escape(sel)} \{{([^}}]*)\}}", css, re.M)
            self.assertIsNotNone(m, sel)
            return m.group(1)
        self.assertIn("color: var(--good-ink)", rule(".good"))
        self.assertIn("color: var(--good-ink)", rule(".board-score .vs-best.good"))
        self.assertIn("color: var(--text-2)", rule(".board-score .vs-best"))
        self.assertNotIn("color", rule(".board-score .vs-par"))
        self.assertIn("background: var(--good)", rule(".meter .m-beat"))
        self.assertIn("var(--good)", rule(".meter .m-tie"))
        self.assertIn("var(--good)", rule("tr.frontier-row td:first-child"))
        self.assertNotIn(".under", css)
        for sel in re.findall(r"^([^{}\n]*(?:\.good|\.vs-best|\.vs-par|\.m-beat|\.m-tie|frontier-row)[^{}\n]*)"
                              r"\{([^}]*)\}", css, re.M):
            with self.subTest(rule=sel[0]):
                self.assertNotRegex(sel[1], r"var\(--(accent|bad|warn)")
        words = {"smaller": True, "faster": True, "better": True, "larger": False, "slower": False, "worse": False,
                 "equal": False}
        seen = {"vs par": set(), "vs it": set(), "first": 0}
        for path in sorted(p for p in self.files if re.fullmatch(r"tasks/[^/]+/(records|reference)/[^/]+\.html", p)):
            raw = self.files[path].decode("utf-8")
            with self.subTest(page=path):
                for green, pct, word in re.findall(r'<dt>vs par</dt><dd>(<span class="good">)?<strong>([^<]+)</strong> '
                                                   r'(\w+)', raw):
                    self.assertEqual(bool(green), words[word], (pct, word))
                    self.assertEqual(pct.startswith("−"), words[word], (pct, word))
                    seen["vs par"].add(word)
                for green, place in re.findall(
                        r'<dt>on this page</dt><dd>(<span class="good">)?<strong>([^<]+)</strong>', raw):
                    first = place in ("best", "smallest", "fastest", "1st")
                    self.assertEqual(bool(green), first, place)
                    seen["first"] += first
                for table in re.findall(r'<table[^>]*class="[^"]*\bcompare\b.*?</table>', raw, re.S):
                    for green, pct, word in re.findall(r'<td[^>]*>(<span class="good">)?<strong>([^<]+)</strong> (\w+)',
                                                       table):
                        self.assertEqual(bool(green), words[word], (pct, word))
                        seen["vs it"].add(word)
        self.assertEqual(seen["vs par"], set(words))
        self.assertTrue({"better", "worse"} <= seen["vs it"], seen["vs it"])
        self.assertGreater(seen["first"], 10)

    def test_latest_lists_every_record_newest_first(self):
        """Decided 2026-11-23 (the owner's request: a way to see the latest submissions to all tasks, sorted by date):
        latest.html lists every record of every task the site shows exactly once, newest first by its date
        (`submitted_at`), one day's records in the front page's task order, then by player and record hash; under a
        heading per day, newest first, written YYYY-MM-DD as the records and their pages write it; every row links
        its record's page and its task's page. A row's score (sky130) is the number the task's leaderboard shows for
        that record (par's records: the front card's Par, with no line under it), and the line under it ends with how
        far it is under or over par, under par (in the good colour, class `good`, decided 2026-11-25) exactly when the
        record's exact score, from its own sky130 columns, is below par's, from the goldens and tests/expected.json
        (how it stands against its task's best: test_pdk.py, on both courses); on the routed course
        a row has a number exactly where the task's routed leaderboard ranks the record, else a dash and why. The nav
        links the page from every page and marks it there, llms.txt lists it, and the front page's strip, after "Try
        it without Lean" and before the steps, shows the five newest rows, each with its date, and links to it."""
        h = self.html("latest.html")
        home = self.files["index.html"].decode("utf-8")
        ref_player = self.config["reference_player"]
        # the front page's task order: its cards
        order = re.findall(r'<li class="task-card">.*?href="tasks/([^/]+)/index.html"', home, re.S)
        shown = sorted((r for r in records() if r["task"] in self.listed),
                       key=lambda r: (order.index(r["task"]), r["player"], r["record_hash"]))
        shown.sort(key=lambda r: r["submitted_at"], reverse=True)
        rows = self.latest_rows(h)
        self.assertEqual([(t, x) for t, x, *_ in rows], [(r["task"], r["record_hash"]) for r in shown])
        self.assertEqual(len({x for _, x, *_ in rows}), len(rows))
        self.assertGreaterEqual(len(rows), 50)
        by_hash = {r["record_hash"]: r for r in shown}
        # the day headings: newest first, ISO dates, each over exactly that day's records
        days = re.findall(r'<section class="latest-day" aria-labelledby="day-([^"]+)"><h2 id="day-\1">([^<]*?) '
                          r'<span class="n">(\d+) records?</span></h2>(.*?)</section>', h, re.S)
        self.assertEqual([d for d, *_ in days], sorted({r["submitted_at"][:10] for r in shown}, reverse=True))
        for day, text, n, body in days:
            with self.subTest(day=day):
                self.assertRegex(day, r"^\d{4}-\d{2}-\d{2}$")
                self.assertEqual(text, day)
                mine = self.latest_rows(body)
                self.assertEqual(int(n), len(mine))
                self.assertTrue(all(by_hash[x]["submitted_at"][:10] == day for _, x, *_ in mine))
        self.assertIn(build.LATEST_DATE_NOTE, text_of(h))
        self.assertIn(build.LATEST_SCORE_NOTE, text_of(h))
        # par's score and each task's board, read off the pages
        cards = {re.search(r'href="tasks/([^/]+)/index.html"', c).group(1):
                 {k: norm(v) for k, v in re.findall(r"<dt>([^<]+)</dt><dd>([^<]+)<", c)}
                 for c in re.findall(r'<li class="task-card">.*?</li>', self.html("index.html"), re.S)}

        def board(task, pdk):
            lb_html = section(self.html(f"tasks/{task}/index.html", pdk), "leaderboard")
            out = {}
            ol = lb_html.split('<ol class="board">', 1)[1].split("</ol>", 1)[0]
            for li in re.findall(r"<li\b[^>]*>.*?</li>", ol, re.S):
                m = re.search(r'records/([0-9a-f]{64})\.html', li)
                if m:
                    out[m.group(1)] = norm(text_of(re.search(r'<div class="board-score">([^<]*)<', li).group(1)))
            return out
        boards = {(t, pdk): board(t, pdk) for t in {r["task"] for r in shown} for pdk in ("sky130", "asap7pnr")}
        for task, x, num, under, li in rows:
            r = by_hash[x]
            with self.subTest(record=x[:12], task=task):
                for tag, attr, ref in parse(li.encode("utf-8")).links:
                    self.assertIn(posixpath.normpath(ref), self.files)
                self.assertIn(f'href="tasks/{task}/index.html"', li)
                self.assertIn(f"<dt>submitted</dt><dd>{r['submitted_at']}</dd>",
                              self.files[f"tasks/{task}/records/{x}.html"].decode("utf-8"))
                if r["player"] == ref_player:
                    self.assertEqual(num, cards[task]["Par"])
                    self.assertIn("badge-par", li)
                    self.assertEqual(under, "")
                    continue
                self.assertEqual(num, boards[(task, "sky130")][x])
                par = par_score(task)
                p = r["ppa"]
                exact = p["area_e4um2_sky130"] * r["score"].get("time_ps", p["delay_ps_sky130"])
                want = ("under par" if exact < par else "equal to par" if exact == par else "over par")
                self.assertTrue(under.endswith(want), (under, exact, par))
                vs_par = re.search(r'<span class="vs-par">(?:<span class="sep"> · </span>)?(.*?)</span></small>', li)
                self.assertEqual(vs_par.group(1).startswith('<span class="good">'), exact < par, vs_par.group(1))
                self.assertNotIn('class="under"', li)        # the accent class it had until 2026-11-25
        for task, x, num, under, li in self.latest_rows(self.html("latest.html", "asap7pnr")):
            with self.subTest(routed=x[:12]):
                if by_hash[x]["player"] == ref_player:
                    continue
                ranked = x in boards[(task, "asap7pnr")]
                self.assertEqual(num != "–", ranked)
                if ranked:
                    self.assertEqual(num, boards[(task, "asap7pnr")][x])
                else:
                    self.assertTrue(under)          # why there is no number ("not placed and routed yet")
        # every page's nav links it, marked on its own page; llms.txt lists it
        for path, data in self.files.items():
            if path.endswith(".html") and path != "404.html":
                with self.subTest(nav=path):
                    nav = re.search(r'<nav class="site-nav"[^>]*>(.*?)</nav>', data.decode("utf-8"), re.S).group(1)
                    self.assertIn(f'href="{build.root_of(path)}latest.html"', nav)
        nav = re.search(r'<nav class="site-nav"[^>]*>(.*?)</nav>', h, re.S).group(1)
        self.assertIn('<a href="latest.html" aria-current="page">Latest</a>', nav)
        self.assertIn("](latest.html)", self.files["llms.txt"].decode("utf-8"))
        # the front page's strip: after "Try it without Lean", before the steps; the five newest, dated; a link to all
        at = [home.index(s) for s in ('id="try-it-without-lean"', f'id="{build.LATEST_ID}"', '<section class="how"')]
        self.assertEqual(at, sorted(at))
        strip = section(self.html("index.html"), build.LATEST_ID)
        top = self.latest_rows(strip)
        self.assertEqual(len(top), 5)
        self.assertEqual([row[:4] for row in top], [row[:4] for row in rows[:5]])
        for task, x, num, under, li in top:
            self.assertIn(f'<span class="latest-date">{by_hash[x]["submitted_at"][:10]}</span>', li)
        self.assertIn('href="latest.html"', strip)
        self.assertIn(f"See all {len(rows)} records", text_of(strip))

    def test_a_card_with_no_record_under_par_says_open(self):
        """Decided 2026-11-17: a front page card of a task where no record is under par (the record is par itself)
        says OPEN in its Under par place, with its meaning on hover, in each course; any other card shows its share.
        Read off the card itself (its Par and Record numbers) and checked against the boards: OPEN on sky130 exactly
        where no ranked record of the task scores below par's design, from the records and the goldens."""
        for pdk in ("sky130", "asap7pnr"):
            cards = re.findall(r'<li class="task-card">.*?</li>', self.html("index.html", pdk), re.S)
            self.assertTrue(cards)
            for card in cards:
                vals = dict(re.findall(r"<dt>([^<]+)</dt><dd>([^<]+)<", card))
                if vals.get("Par") in (None, "–"):
                    continue
                with self.subTest(pdk=pdk, card=vals):
                    open_ = vals["Under par"] == build.OPEN_WORD
                    self.assertEqual(open_, vals["Par"] == vals["Record"])
                    if open_:
                        self.assertIn(f'<div class="stat stat-open" title="{build.esc(build.OPEN_TITLE)}">', card)
        cards = {re.search(r'href="tasks/([^/]+)/index.html"', c).group(1): c for c in
                 re.findall(r'<li class="task-card">.*?</li>', self.html("index.html", "sky130"), re.S)}
        for t in self.ranked:
            par = par_score(t)
            if par is None:
                continue
            board = lb.build_board(lb.load_task(os.path.join(SVGOLF, "tasks"), t),
                                   [r for r in records() if r["task"] == t and r["player"] != self.config["reference_player"]],
                                   flow=pinned_flow("seq" if build.metrics.is_clocked(lb.load_task(
                                       os.path.join(SVGOLF, "tasks"), t)) else "comb"))
            recs = {r["record_hash"]: r for r in records()}
            ranked = [recs[r["record_hash"]]["ppa"] for r in board["frontier"] + board["dominated"]]
            beats = any(p["area_e4um2_sky130"] * p["delay_ps_sky130"] < par for p in ranked)
            with self.subTest(task=t):
                self.assertEqual(build.OPEN_WORD in text_of(cards[t]), not beats)

    def test_the_routed_course_is_consistent(self):
        """Decided 2026-11-17 (the routed ASAP7 course): reproduce.html has a section on the routed course (the pinned
        image by its digest, score/pnr/'s commands) that names the adder's par's routed number and its cells-only
        number as two quantities; "wire cost" is gone (the routed score against the cells-only one: negative on some
        designs, not the wires' cost alone, never analysed); the front page's "How it works" quotes, on the routed
        course, that course's par of the adder, the number its task page shows; and an under-par share that would
        round to 0% keeps its digits (the routed fdivp's record beat par by about a third of a percent and said 0%)."""
        self.assertEqual(build.under_text(0.0035), "0.35%")
        self.assertEqual(build.under_text(0.004999), "0.5%")
        self.assertEqual(build.under_text(0), "0%")
        self.assertEqual(build.under_text(0.68), "68%")
        self.assertEqual(build.under_text(-0.003), "0.3% over par")
        rp = self.files["reproduce.html"].decode("utf-8")
        routed = section(rp, build.REPRODUCE_ROUTED) if f'<section id="{build.REPRODUCE_ROUTED}"' in rp else \
            rp[rp.index(f'id="{build.REPRODUCE_ROUTED}"'):]
        text = norm(text_of(routed))
        with open(os.path.join(SVGOLF, "score", "pnr", "pins.json"), encoding="utf-8") as fh:
            img = json.load(fh)["course"]["image"]
        self.assertIn(img["manifest_digest"], text)
        for said in ("score/pnr/job.py", "score/pnr/run_job.py run", "Two different numbers for one design",
                     "placed and routed, wires included", "before place and route and without wires"):
            self.assertIn(said, text)
        add_page = self.html("tasks/add/index.html", "asap7pnr")
        par_routed = re.search(r"<dt>(?:<a [^>]*>)?Par[^<]*(?:</a>)?</dt><dd>([^<]+)<",
                               section(add_page, "numbers")).group(1)
        self.assertIn(f"scores {par_routed} µm²·ns", text)
        for path, data in self.files.items():
            if path.endswith(".html"):
                self.assertNotIn("wire cost", text_of(data), path)
        home_a7 = self.html("index.html", "asap7pnr")
        note = norm(text_of(re.search(r'<p class="pdk-asap7pnr pdk-note small">On this course.*?</p>', home_a7,
                                      re.S).group(0)))
        self.assertIn(f"the adder's par is {par_routed} µm²·ns", note)
        self.assertNotIn("On this course, ASAP7 placed and routed", text_of(self.html("index.html", "sky130")))
        for pdk in ("sky130", "asap7pnr"):
            cards = re.findall(r'<li class="task-card">.*?</li>', self.html("index.html", pdk), re.S)
            for card in cards:
                vals = dict(re.findall(r"<dt>([^<]+)</dt><dd>([^<]+)<", card))
                if "Under par" in vals and vals.get("Par") not in (None, "–") and vals["Par"] != vals["Record"]:
                    with self.subTest(pdk=pdk, card=vals):
                        self.assertNotEqual(vals["Under par"], "0%")

    def test_the_boards_provenance_is_said_with_the_records_counts(self):
        """Decided 2026-11-17: who made the board's records, said plainly. The front page says in one sentence under the
        task cards that the maintainers seeded the board and how many records were made with AI assistance, linking
        About's "Who made the records", which says it with the counts of the records (counted here independently of
        the generator: every record names its assistant, the proofs ported by the maintainers, the entries whose design
        file is byte for byte a reference design), the newcomer study and what the marks mean. Every player's entry
        whose design file is byte for byte a file under tasks/*/reference/ carries the mark "reference design", naming
        the file on hover, on its task's board (both courses) and on its own page; no other row or page does."""
        recs = [r for r in records() if r["task"] in self.listed]
        ref_player = self.config["reference_player"]
        refs = {}
        for path in sorted(glob.glob(os.path.join(SVGOLF, "tasks", "*", "reference", "*.sv"))):
            with open(path, "rb") as fh:
                refs.setdefault(hashlib.sha256(fh.read()).hexdigest(),
                                posixpath.relpath(path, SVGOLF).replace(os.sep, "/"))
        entries = [r for r in recs if r["player"] != ref_player]
        copies = [r for r in entries if r["files"]["sv"]["sha256"] in refs]
        self.assertTrue(copies)
        assisted = [r for r in recs if r["assisted_by"]]
        ported = [r for r in recs if (r.get("remade") or {}).get("proof") == "maintainer port"]
        words = (f"all {len(recs)} records were made with AI assistance" if len(assisted) == len(recs) else
                 f"{len(assisted)} of the {len(recs)} records name the AI systems or tools that helped")
        # since 2026-11-24 the board also holds records of players outside the maintainers (build.OUTSIDE_PLAYERS, each
        # handle a player of the board): both places count them
        outside = [r for r in recs if r["player"] in build.OUTSIDE_PLAYERS]
        players = {r["player"] for r in recs}
        for h in build.OUTSIDE_PLAYERS:
            self.assertIn(h, players)
            self.assertNotEqual(h, ref_player)
        self.assertTrue(outside)
        k = len({r["player"] for r in outside})
        out = f"{len(outside)} of the {len(recs)} records come from " + ("a player" if k == 1 else f"{k} players") \
            + " outside the maintainers"
        home = self.files["index.html"].decode("utf-8")
        cards_end = home.index("</ul>", home.index('<ul class="task-cards">'))
        note = re.match(r'</ul><p class="board-note">(.*?)</p></section>', home[cards_end:], re.S)
        self.assertIsNotNone(note, home[cards_end:cards_end + 300])
        self.assertEqual(norm(text_of(note.group(1))), f"The board was seeded by the maintainers, and {out}: {words}, "
                         "each naming its assistant (who made the records).")
        self.assertIn('href="about.html#who-made-the-records"', note.group(1))
        about = self.files["about.html"].decode("utf-8")
        sec = about[about.index('id="who-made-the-records"'):]
        sec = norm(text_of(sec[:sec.index("<h2")]))
        self.assertNotIn("The board so far was seeded by the maintainers.", sec)
        for said in ("The board was seeded by the maintainers.", out[:1].upper() + out[1:],
                     ", ".join(sorted({r["player"] for r in outside})) + "): handed in by pull request, each was made "
                     "again by the maintainers on the rating machine under the player's handle",
                     words[:1].upper() + words[1:],
                     "Several came from a newcomer study run by the maintainers",
                     f"{len(ported)} of the {len(recs)} proofs are marked as ported: the maintainers re-made them",
                     f'{len(copies)} of the {len(entries)} entries carry the mark "reference design"',
                     "They are entries like any other and are ranked as usual."):
            self.assertIn(said, sec)
        # the words without an outside record (the board before 2026-11-24) and with several outside players
        p0 = {"records": 5, "assisted": 5, "ported": 0, "entries": 4, "copies": 0, "outside": 0, "outside_players": []}
        self.assertIsNone(build.outside_words(p0))
        self.assertIn("The board so far was seeded by the maintainers: all 5 records", build.provenance_front_html(p0, ""))
        self.assertTrue(build.provenance_md(p0).startswith("The board so far was seeded by the maintainers. All 5"))
        p2 = dict(p0, outside=3, outside_players=["a-player", "b-player"])
        self.assertEqual(build.outside_words(p2), "3 of the 5 records come from 2 players outside the maintainers")
        self.assertIn("(`a-player`, `b-player`): handed in by pull request", build.provenance_md(p2))
        self.assertEqual(norm(text_of(about)).count("made with AI assistance"), 1)       # said once on the page
        mark = re.compile(r'<span class="badge badge-reference" title="byte for byte ([^"]+)">reference design</span>')
        for t in self.ranked:
            board = section(self.files[f"tasks/{t}/index.html"].decode("utf-8"), "leaderboard")
            for r in (x for x in entries if x["task"] == t):
                with self.subTest(task=t, record=r["record_hash"][:12]):
                    page_ = self.files[f"tasks/{t}/records/{r['record_hash']}.html"].decode("utf-8")
                    head = page_[page_.index('<header class="page-head">'):]
                    head = head[:head.index("</header>")]
                    rows = [li for li in re.findall(r"<li\b.*?</li>", board, re.S)
                            if f'records/{r["record_hash"]}.html"' in li]
                    want = refs.get(r["files"]["sv"]["sha256"])
                    if want is None:
                        self.assertNotIn("reference design", head)
                        self.assertTrue(all("reference design" not in li for li in rows))
                        continue
                    self.assertEqual(mark.findall(head), [want])
                    self.assertTrue(rows)
                    for li in rows:
                        self.assertEqual(mark.findall(li), [want])
                    self.assertTrue(os.path.isfile(os.path.join(SVGOLF, *want.split("/"))))
            for r in (x for x in recs if x["task"] == t and x["player"] == ref_player):
                page_ = self.files[f"tasks/{t}/records/{r['record_hash']}.html"].decode("utf-8")
                head = page_[page_.index('<header class="page-head">'):]
                self.assertNotIn("badge-reference", head[:head.index("</header>")])

    def test_home_steps_on_the_adder_follow_the_task_cards(self):
        """The whole idea, on the adder: the three steps come after the hero, the heading "Tasks" (since 2026-11-13 the
        block over the cards holds nothing else) and the task cards (decided 2026-11-06); step 1 quotes the reference `add_n.sv` without its comments, byte for
        byte; step 3's last line is the line check.py prints for it (check.py's own `ranked_headline`, par
        from the goldens), and home.md types none of it."""
        html_ = self.files["index.html"].decode("utf-8")
        order = [html_.index(s) for s in ('<header class="hero', '<h2>Tasks</h2>', '<ul class="task-cards">',
                                          '<section class="how"')]
        self.assertEqual(order, sorted(order))
        how = html_[html_.index('<section class="how"'):html_.index("</section>", html_.index('<section class="how"'))]
        self.assertEqual(len(re.findall(r"<ol\b", how)), 1)
        self.assertEqual(how.count("</li>"), 3)
        for word in ("Write", "Prove", "Check", "You submit two files"):
            self.assertIn(word, text_of(how))
        blocks = [html.unescape(re.sub(r"<[^>]+>", "", b)) for b in re.findall(r"<pre\b[^>]*>(.*?)</pre>", how, re.S)]
        src = read_text_file("tasks/add/reference/add_n.sv")
        self.assertEqual(blocks[0] + "\n", "".join(ln for ln in src.splitlines(True) if not ln.startswith("//")))
        self.assertIn("theorem solution : Goal := by", blocks[1])
        # the line check.py prints, from its own code: the add_n golden, par the par design (leaderboard/par.json)
        with open(os.path.join(SVGOLF, "score", "tests", "ppa", "designs.json"), encoding="utf-8") as fh:
            name = next(d["name"] for d in json.load(fh)["designs"]
                        if d["src"] == "tasks/add/reference/add_n.sv" and d["task"] == "add")
        with open(os.path.join(SVGOLF, "score", "tests", "ppa", "expected_ppa.json"), encoding="utf-8") as fh:
            gold = json.load(fh)["designs"][name]
        task = lb.load_task(os.path.join(SVGOLF, "tasks"), "add")
        scores = sky130_scores("add")
        par_stem = lb.par_stem(os.path.join(SVGOLF, "tasks"), task)
        self.assertIn(next(iter(lb.par_names(os.path.join(SVGOLF, "tasks"), task))), scores)
        spec = importlib.util.spec_from_file_location("svgolf_check_py_site", os.path.join(SVGOLF, "check.py"))
        checkpy = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(checkpy)
        res = {"task": "add", "stages": {"ppa": {}}, "score": {},
               "ppa": {"available": True, "area_e4um2_sky130": gold["area_e4um2"],
                       "area_um2_sky130": gold["area_e4um2"] / 10000, "delay_ps_sky130": gold["delay_ps"]}}
        par = {"name": par_stem, "um2ns": build.combined.um2ns(par_score("add"))}
        checkpy.task_par = lambda _task: (par, None)
        line = checkpy.ranked_headline(res)
        self.assertTrue(line.startswith("ranked (sky130 A0'): "), line)
        self.assertEqual(blocks[2].rstrip("\n").split("\n")[-1], line)
        self.assertIn("python3.12 check.py tasks/add solution.sv Solution.lean", blocks[2])
        home_md = read_text_file("site/content/home.md")
        self.assertNotIn("assign", home_md)
        self.assertNotIn("ranked (sky130", home_md)
        self.assertEqual([m.group(0) for m in build.HAND_TYPED.finditer(build.HOME_PLACEHOLDER.sub("", home_md))], [])

    def test_every_page_draws_its_logo_and_head_flag_as_decoration(self):
        """The art outside the home hero: the logo in the header and the footer (pixelart.logo) and
        the flag at the end of each page head's rule (pixelart.hole_flag), aria-hidden with no text,
        so a page's text is its content alone."""
        for path in self.pages:
            html_ = self.files[path].decode("utf-8")
            with self.subTest(page=path):
                self.assertEqual(html_.count('<svg class="px logo"'), 2)
                self.assertEqual(html_.count('<svg class="px hole-flag"'), html_.count('<header class="page-head">'))
                for svg in re.findall(r'<svg class="px [^"]*".*?</svg>', html_, re.S):
                    self.assertIn('aria-hidden="true"', svg)
                    self.assertEqual(text_of(svg), "")
                brand = html_[html_.index('<a class="brand"'):html_.index("</a>", html_.index('<a class="brand"'))]
                self.assertEqual(text_of(brand), "svGolf")

    def test_home_defines_ls_sv_with_a_link_where_it_first_appears(self):
        html_ = self.files["index.html"].decode("utf-8")
        first = html_.index("ls-sv")
        self.assertTrue(html_[:first].endswith('">'), "the first ls-sv is a link text")
        self.assertIn("formal semantics of SystemVerilog", text_of(html_[first:first + 400]))

    def test_home_does_not_overclaim_the_post_synthesis_check(self):
        home = norm(text_of(self.files["index.html"]))
        about = norm(text_of(self.files["about.html"]))
        for text in (home, about):
            self.assertNotIn("the circuit that was proved is the circuit that was scored", text)
            self.assertNotIn("fixed set of vectors", text)
            self.assertNotIn("closes the gap", text)
        self.assertIn("sample of input vectors", home)
        self.assertIn("sampling, not a proof", home)
        # the salt as it is (2026-11-11: no record so far was checked with one; test_the_claims_on_home_and_about_hold)
        self.assertIn("a secret salt can make them unpredictable", home)

    def test_two_builds_are_byte_identical(self):
        other = os.path.join(self.tmp.name, "again")
        env = dict(os.environ, PYTHONHASHSEED="4242")   # a different hash seed: set order must not leak
        proc = subprocess.run([sys.executable, BUILD_PY, "--offline", "--out", other], capture_output=True,
                              text=True, env=env, cwd=SVGOLF)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        again = read_tree(other)
        self.assertEqual(sorted(again), sorted(self.files))
        self.assertEqual([p for p in sorted(again) if again[p] != self.files[p]], [])

    def test_no_denylisted_string_in_the_output(self):
        # (the private markers are kept outside the repository: `build.py --denylist`)
        deny = [w.lower() for w in self.config["denylist"] if isinstance(w, str)]
        for path, data in self.files.items():
            text = data.decode("utf-8", errors="replace").lower()
            for w in deny:
                self.assertNotIn(w, text, f"{path} contains {w!r}")

    def test_no_internal_marker_in_the_sites_own_text(self):
        """The internal markers (names, work-package codes, review rounds) do not occur in what the
        site writes itself: every page without its verbatim <pre data-src> blocks and without what
        players wrote, plus the generated data and llms.txt (the files offered byte for byte are the
        repository's)."""
        markers = [e for e in self.config["denylist"] if isinstance(e, dict)]
        players = set()
        for r in records():
            # the notes, and their first sentence, which a record page with a writeup shows alone (2026-11-25)
            players.update([r["player"], *r["assisted_by"], r.get("notes") or "",
                            build.note_parts(r.get("notes") or "")[0]])
        for path, data in sorted(self.files.items()):
            if not (path.endswith(".html") or path.startswith("data/") or path == "llms.txt"):
                continue
            text = data.decode("utf-8")
            if path.endswith(".html"):
                text = re.sub(r'<pre[^>]* data-src="[^"]*"[^>]*>.*?</pre>', "", text, flags=re.S)
                # a record's notes and assisted-by rows: what the player wrote, its names linked (2026-11-23)
                text = re.sub(r"(<dt>(?:notes|assisted by)</dt><dd>)(.*?)(</dd>)",
                              lambda m: m.group(1) + build.esc(player_words(m.group(2))) + m.group(3), text, flags=re.S)
                text = html.unescape(text)
            for p in sorted(players, key=len, reverse=True):
                if p:
                    text = text.replace(p, "")
            text = text.lower()
            for m in markers:
                if path in m.get("allow", {}):
                    continue
                self.assertNotIn(m["text"].lower(), text, f"{path} contains the internal marker {m['text']!r}")

    def test_a_marker_in_a_player_proof_passes_only_by_the_file_block_exemption(self):
        """Decided 2026-11-13: with the diff view gone, what a player wrote in a design or a proof reaches a record page
        only in its verbatim file blocks (`<pre data-src>`), which the internal-marker guard exempts as it exempts every
        repository file shown byte for byte; no exemption was added for it. Measured on the tree's own records (the
        matmul proofs name an internal statement name in a comment): every record page whose files carry a marker
        passes the guard as built, and fails it with that one exemption taken away, on exactly those markers, so no
        other part of the page carries the files' text. The guard runs in every build, the strict one included. (The
        markers are checked here without their allowances, which name other pages: no record page is allowed one.)"""
        markers = [{k: v for k, v in e.items() if k != "allow"} for e in self.config["denylist"] if isinstance(e, dict)]
        self.assertFalse(any(p.startswith("tasks/") and "/records/" in p for e in self.config["denylist"]
                             if isinstance(e, dict) for p in e.get("allow", {})))
        players = set()
        for r in records():
            players.update([r["player"], *r["assisted_by"], r.get("notes") or ""])
        pages = {}
        for r in records():
            text = "".join(read_text_file(f"leaderboard/data/{r['task']}/{r['record_hash']}{ext}")
                           for ext in (".sv", ".lean")).lower()
            hit = sorted(m["text"] for m in markers if m["text"].lower() in text)
            if hit:
                pages[f"tasks/{r['task']}/records/{r['record_hash']}.html"] = hit
        self.assertTrue(any(p.startswith("tasks/matmul/") for p in pages), "no player proof names a marker any more")
        files = {p: self.files[p] for p in pages}
        self.assertEqual(build.check_denylist(files, markers, copies=set(), player_text=players), [])
        with mock.patch.object(build, "VERBATIM_BLOCK", re.compile(r"(?!)")):
            hits = build.check_denylist(files, markers, copies=set(), player_text=players)
        self.assertEqual(sorted(hits), sorted(f"{p}: contains the internal marker {m!r} (denylist, scope site-text)"
                                              for p, ms in pages.items() for m in ms))

    def test_the_public_markers_and_the_docs_without_them(self):
        """Decided 2026-11-11: config.json's denylist holds the public markers of what is internal (work-package
        codes, the clocked statements' internal name, the plan files, a development path, process words, a status
        note), each with its reason, allowed only where the site shows text it may not change (verbatim Lean text,
        README's one quote of the old name; since 2026-11-13 no longer the Refusals page, which shows the refusal
        register's rows only behind folds and in plain words); and the documents a player reads carry no
        work-package code and write dates in one format."""
        markers = {e["text"]: e for e in self.config["denylist"] if isinstance(e, dict)}
        self.assertEqual(sorted(markers), sorted(["WP-", "txtask-v", "PLAN.md", "PLAN2.md", "PLAN4.md",
                                                  "svgolf/site/build.py", "newcomer study", "awaiting confirmation"]))
        for text, m in markers.items():
            self.assertEqual(m["scope"], "site-text", text)
            self.assertTrue(m["why"], text)
        self.assertEqual(sorted(markers["txtask-v"]["allow"]),
                         sorted(["rules.html", "tasks/matmul/index.html", "tasks/sorter/index.html"]))
        for text in ("WP-", "PLAN.md", "PLAN2.md", "PLAN4.md", "svgolf/site/build.py", "awaiting confirmation"):
            self.assertNotIn("allow", markers[text])
        # decided 2026-11-17: About's "Who made the records" names the newcomer study the maintainers ran
        self.assertEqual(sorted(markers["newcomer study"]["allow"]), ["about.html"])
        docs = ["README.md", "PROVING.md", "CONTRIBUTING.md", "score/PPA.md", "leaderboard/README.md"]
        docs += sorted(posixpath.relpath(p, SVGOLF).replace(os.sep, "/")
                       for p in glob.glob(os.path.join(SVGOLF, "tasks", "*", "README.md"))
                       + glob.glob(os.path.join(SVGOLF, "tasks", "*", "*", "README.md")))
        for rel in docs:
            with self.subTest(doc=rel):
                text = read_text_file(rel)
                self.assertNotIn("WP-", text)
                self.assertFalse(re.search(r"(?<![\d/.:-])1[01]/[0-3]\d(?![\d/])", text), "a MM/DD date")
        # the one quote of the old name, on purpose (README's clocked rules)
        self.assertEqual(read_text_file("README.md").count("txtask-v"), 1)


class GuardTest(unittest.TestCase):
    """The build's own guards fire."""

    def build(self, **kw):
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return build.build_site(offline=True, **kw)

    def test_strict_build_passes(self):
        site = self.build(strict=True)
        self.assertEqual(site.warnings, [])

    def test_the_refusals_cards_follow_the_register(self):
        """content/refusals.json against the refusal register (`refusal_cards`): a row the register does not have (a
        lifted refusal), an svGolf row on no card, a row named twice and a card without what to write instead each
        fail the build."""
        config = build.load_config()
        reg = json.loads(build.read_text(config["refusals_json"]))
        content = json.loads(build.read_text(build.REFUSALS_CONTENT))
        build.refusal_cards(reg, content)
        lifted = json.loads(json.dumps(reg))
        lifted["svgolf"]["entries"] = [e for e in lifted["svgolf"]["entries"] if e["id"] != "sg-ban-cmp"]
        with self.assertRaisesRegex(build.BuildError, "does not have.*sg-ban-cmp"):
            build.refusal_cards(lifted, content)
        added = json.loads(json.dumps(reg))
        added["svgolf"]["entries"].append(dict(added["svgolf"]["entries"][0], id="sg-new-row"))
        with self.assertRaisesRegex(build.BuildError, "sg-new-row.*on no card"):
            build.refusal_cards(added, content)
        twice = json.loads(json.dumps(content))
        twice["groups"][0]["more"].append(twice["groups"][0]["cards"][0]["rows"][0])
        with self.assertRaisesRegex(build.BuildError, "twice"):
            build.refusal_cards(reg, twice)
        bare = json.loads(json.dumps(content))
        card = bare["groups"][0]["cards"][0]
        card.pop("instead", None)
        card.pop("instead_text", None)
        with self.assertRaisesRegex(build.BuildError, "what to write instead"):
            build.refusal_cards(reg, bare)

    def test_placeholders_fill_from_the_data_and_refuse_the_rest(self):
        site = build.Site(build.load_config())
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            tasks = build.collect(site, True)
        add = next(t for t in tasks if t.name == "add")
        m = build.placeholder_metrics(add, "add_n")
        self.assertEqual(build.fill_placeholders(site, add, "{{add_n.area}} at {{ add_n.time }}", "x.md"),
                         f"{build.area_text(m['area_um2'])} µm² at {build.ns(m['time_ps'])} ns")
        self.assertEqual(build.fill_placeholders(site, add, "{{par.depth}}", "x.md"), str(m["depth"]))
        for bad in ("{{nosuch.area}}", "{{add_n.colour}}"):
            with self.assertRaises(build.BuildError):
                build.fill_placeholders(site, add, bad, "x.md")
        n = len(site.warnings)
        build.fill_placeholders(site, add, "a 2.59 ns path and 460.4 µm²", "x.md")
        self.assertEqual(len(site.warnings), n + 2)
        # home.md's: a task-qualified field, check.py's line, a design's source alone on its (indented) line
        self.assertEqual(build.fill_home(site, tasks, "{{add/add_n.area}}", "h.md"), f"{build.area_text(m['area_um2'])} µm²")
        self.assertTrue(build.fill_home(site, tasks, "{{add/par.headline}}", "h.md").startswith("ranked (sky130 A0'): "))
        # a clocked design's line is check.py's clocked one, cycles x period (decided 2026-11-11)
        mm = next(t for t in tasks if t.name == "matmul")
        d = build.par_design(mm)
        spec = importlib.util.spec_from_file_location("svgolf_check_py_headline", os.path.join(SVGOLF, "check.py"))
        checkpy = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(checkpy)
        checkpy.task_par = lambda _task: ({"name": d["name"], "um2ns": build.combined.um2ns(d["exact"])}, None)
        res = {"task": "matmul", "stages": {"ppa": {}},
               "ppa": {"available": True, "area_e4um2_sky130": round(d["m"]["area_um2"] * 10000),
                       "area_um2_sky130": d["m"]["area_um2"], "delay_ps_sky130": d["m"]["period_ps"]},
               "score": {k: d["m"][k] for k in ("time_ps", "cycles", "period_ps")}}
        line = build.check_headline(mm, d)
        self.assertIn(f" um^2 x {d['m']['cycles']} cycles x {d['m']['period_ps']} ps = ", line)
        self.assertEqual(line, checkpy.ranked_headline(res))
        sv = build.fill_home(site, tasks, "   {{add/add_n.sv}}", "h.md").split("\n")
        self.assertEqual(sv[0], "   module add_n #(parameter int N = 16) (")
        self.assertEqual(sv[-1], "   endmodule")
        for bad in ("{{nosuch/add_n.area}}", "{{add/nosuch.area}}", "{{add/add_n.colour}}", "x {{add/add_n.sv}}"):
            with self.assertRaises(build.BuildError):
                build.fill_home(site, tasks, bad, "h.md")
        n = len(site.warnings)
        build.fill_home(site, tasks, "par is 1202.21 um^2", "h.md")
        self.assertEqual(len(site.warnings), n + 1)

    def test_a_new_design_card_must_name_its_route(self):
        """The card comes from the README; one that does not name its kind's route fails the build, a ranked
        task without one is a warning, fatal under --strict."""
        site = build.Site(build.load_config())
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            tasks = build.collect(site, True)
        sbox = next(t for t in tasks if t.name == "aes_sbox")
        real = site.doc_text
        self.assertIn("sv_exhaustive", build.new_design_html(site, sbox, sbox.page, build.md.Slugger([])))
        site.doc_text = lambda rel: real(rel).replace("sv_exhaustive", "sv_whatever")
        with self.assertRaises(build.BuildError):
            build.new_design_html(site, sbox, sbox.page, build.md.Slugger([]))
        self.assertIn(f"\n## {build.NEW_DESIGN}\n", real("svgolf/tasks/aes_sbox/README.md"))
        site.doc_text = lambda rel: real(rel).replace(f"## {build.NEW_DESIGN}", "## Something else")
        n = len(site.warnings)
        self.assertEqual(build.new_design_html(site, sbox, sbox.page, build.md.Slugger([])), "")
        self.assertEqual(len(site.warnings), n + 1)
        site.strict = True
        with self.assertRaises(build.BuildError):
            build.new_design_html(site, sbox, sbox.page, build.md.Slugger([]))

    def test_the_page_shows_a_card_s_parts_only_while_the_readme_still_has_them(self):
        """2026-11-09: the page shows none of the card's opening (the task section states it), the route and,
        folded, the rest; 2026-11-11: the commands are How to submit's first two, with what they do (or the task's
        site text, which must explain the same options) under them. A card with no route paragraph, a site text that
        drops an option the README explains, or a code block that is not the two commands, fails the build."""
        site = build.Site(build.load_config())
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            tasks = build.collect(site, True)
        by = {t.name: t for t in tasks}
        add, arb = by["add"], by["arbiter"]
        real, content = site.doc_text, site.content
        checks, html_ = build.new_design_parts(site, add, add.page, build.md.Slugger([]))
        self.assertEqual(build.new_design_html(site, add, add.page, build.md.Slugger([])), html_)
        self.assertTrue(html_.startswith("<p><strong>The route"), html_[:80])
        self.assertNotIn("A new adder is your own", html_ + checks)
        self.assertNotIn("Find the design without Lean", html_ + checks)
        self.assertIn("The second command runs every stage that needs no proof", checks)
        self.assertNotIn("score/ppa.py solution.sv", html_)
        self.assertIn(f'<details class="nd-detail" id="{build.NEW_DESIGN_FOLD}"><summary>The proof in detail', html_)
        # How to submit's first two commands are the card's, wrapped
        card = build.new_design_card(site, add)
        self.assertEqual([c for c, _ in card.commands("add")],
                         ["python3.12 score/ppa.py solution.sv --task tasks/add --no-mapped --path",
                          "python3.12 check.py tasks/add solution.sv --unproved --tactics --stage-dir stage"])
        self.assertIn("# the golfing loop, no Lean: area, delay and the critical\n"
                      "#    path, about a second\n"
                      "python3.12 score/ppa.py solution.sv --task tasks/add \\\n    --no-mapped --path\n"
                      "# ... and the same design on ASAP7 (Step 0's five files)\n"
                      "python3.12 score/ppa.py --pdk asap7 solution.sv \\\n    --task tasks/add --no-mapped\n"
                      "# 1. no proof needed; ", build.submit_commands(add, card))
        cases = ((lambda s: s.replace("**The route: the `sv_comb`", "**A route: the `sv_comb`"), "no route paragraph"),
                 (lambda s: s.replace("--unproved --tactics --stage-dir stage\n",
                                      "--unproved --tactics --stage-dir stage\nls stage\n", 1), "holds the two commands"),
                 (lambda s: s.replace("python3.12 score/ppa.py solution.sv --task tasks/add --no-mapped",
                                      "python3.12 score/ppa.py solution.sv --task tasks/add --no-mapped | tail", 1),
                  "holds the two commands"))
        for edit, why in cases:
            with self.subTest(why=why):
                site.doc_text = lambda rel, edit=edit: edit(real(rel)) if rel == f"{add.dir}/README.md" else real(rel)
                with self.assertRaisesRegex(build.BuildError, why):
                    build.new_design_html(site, add, add.page, build.md.Slugger([]))
        site.doc_text = real
        dropped = dict(content("tasks/arbiter.json"))
        dropped["new_design_checks"] = dropped["new_design_checks"].replace("(`--path`)", "")
        site.content = lambda rel: dropped if rel == "tasks/arbiter.json" else content(rel)
        with self.assertRaisesRegex(build.BuildError, "does not explain --path"):
            build.new_design_html(site, arb, arb.page, build.md.Slugger([]))
        site.content = content
        # a latency kind's run without a proof must give --latency (check.py's usage rule)
        mm = by["matmul"]
        site.doc_text = lambda rel: (real(rel).replace("--unproved --latency 4 --stage-dir stage",
                                                       "--unproved --stage-dir stage", 1)
                                     if rel == f"{mm.dir}/README.md" else real(rel))
        with self.assertRaisesRegex(build.BuildError, "must give `--latency n`"):
            build.submit_commands(mm, build.new_design_card(site, mm))
        site.doc_text = real

    def test_a_second_form_of_a_command_fails_the_build(self):
        """2026-11-11: each command How to submit shows is on a task page once (build.commands_once): a page that
        shows another form of one (a quick start, the README's commands in the card) fails the build; the tutorial,
        whose walk-through runs them again, is exempt."""
        site = build.Site(build.load_config())
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            tasks = build.collect(site, True)
        by = {t.name: t for t in tasks}
        for name in ("matmul", "add"):
            with self.subTest(task=name):
                t = by[name]
                cmds = build.submit_commands(t, build.new_design_card(site, t))
                once = build.page.code_block(cmds, "bash") + build.page.code_block(build.reference_copy(t), "bash")
                build.commands_once(t, once, cmds)
                unproved = next(ln for ln in cmds.replace(" \\\n    ", " ").split("\n")
                                if " --unproved" in ln and not ln.startswith("#"))
                with self.assertRaisesRegex(build.BuildError, "on the page 2 times"):
                    build.commands_once(t, once + f"<pre>{unproved.split(' --unproved')[0]} --unproved</pre>", cmds)
                # a second form without the interpreter, as a score tip once named it (review 2026-11-11)
                with self.assertRaisesRegex(build.BuildError, "on the page 2 times"):
                    build.commands_once(t, once + f"<p><code>score/ppa.py solution.sv --task tasks/{name} --path</code> "
                                                  "names the critical path</p>", cmds)
                with self.assertRaisesRegex(build.BuildError, "on the page 0 times"):
                    build.commands_once(t, build.page.code_block(cmds, "bash"), cmds)
        tut = by["_example"]
        cmds = build.submit_commands(tut)
        build.commands_once(tut, build.page.code_block(cmds + cmds, "bash"), cmds)

    def test_a_readme_edit_where_the_page_shows_its_own_text_warns(self):
        """2026-11-09 (review L8): the page shows its own text in place of the README card's opening and, where
        `new_design_checks` replaces it, of its text on the two commands; content/tasks/<t>.json
        `new_design_reviewed` pins what the page was last checked against. An edit there (a new fact the page would
        not show) is a warning, fatal under --strict, that names the new fingerprint; the pinned text builds
        clean."""
        site = build.Site(build.load_config())
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            tasks = build.collect(site, True)
        by = {t.name: t for t in tasks}
        real = site.doc_text
        for name, old, new, key in (
                ("add", "A new adder is your own", "A new adder, any carry scheme, is your own", "opening"),
                ("arbiter", "A wrong policy is named there", "A wrong policy is named there at once", "checks")):
            with self.subTest(task=name):
                t = by[name]
                site.warnings = []
                build.new_design_html(site, t, t.page, build.md.Slugger([]))
                self.assertEqual([w for w in site.warnings if "new_design_reviewed" in w], [])
                readme = f"{t.dir}/README.md"
                self.assertIn(old, real(readme))
                site.doc_text = lambda rel, readme=readme, old=old, new=new: (
                    real(rel).replace(old, new, 1) if rel == readme else real(rel))
                build.new_design_html(site, t, t.page, build.md.Slugger([]))
                hit = [w for w in site.warnings if f"new_design_reviewed.{key}" in w]
                self.assertEqual(len(hit), 1, site.warnings)
                self.assertIn(new, hit[0])
                site.doc_text = real

    def test_a_task_text_that_leaves_out_a_banned_operator_warns(self):
        """2026-11-09 (review M3): the task text is the page's one statement of the bans, so it must name every
        operator the task bans in a code span, the ordering comparisons included where `+` or `-` is banned."""
        site = build.Site(build.load_config())
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            tasks = build.collect(site, True)
        add = next(t for t in tasks if t.name == "add")
        self.assertEqual(build.banned_operators(add.task)[-4:], ["<", "<=", ">", ">="])
        site.warnings = []
        build.statement_html(site, add, add.page, build.md.Slugger([]))
        self.assertEqual(site.warnings, [])
        path = f"{build.CONTENT}/tasks/add.md"
        real = build.read_text
        try:
            build.read_text = lambda rel: (real(rel).replace(" and the ordering comparisons `< <= > >=`", "")
                                           if rel == path else real(rel))
            build.statement_html(site, add, add.page, build.md.Slugger([]))
        finally:
            build.read_text = real
        self.assertEqual(len(site.warnings), 1, site.warnings)
        self.assertIn("< <= > >=", site.warnings[0])

    def test_a_tie_with_par_leaves_the_record_at_par(self):
        """Par and an earlier-dated entry with exactly par's score: the Record names par ('with no
        submissions it is par'), and nothing is under par."""
        class T:
            pass
        t = T()
        t.refs = [{"stem": "a"}, {"stem": "b"}]
        par = {"kind": "reference", "exact": 10, "date": "2026-11-02", "stem": "a", "sha": "1", "id": "reference/a",
               "par": True, "name": "a", "m": {"adp": 1e-6}}
        tie = dict(par, date="2026-11-01", stem="b", sha="2", id="reference/b", par=False, name="b")
        t.designs = [par, tie]
        h = build.headline(t)
        self.assertEqual((h["record_name"], h["under"]), ("a", 0.0))

    def test_a_denylist_hit_fails_the_build(self):
        config = build.load_config()
        config["denylist"] = config["denylist"] + ["Pareto frontier"]
        with self.assertRaises(build.BuildError) as e:
            self.build(config=config)
        self.assertIn("Pareto frontier", str(e.exception))

    def test_a_stale_redaction_fails_the_build(self):
        config = build.load_config()
        config["redact"] = config["redact"] + [{"file": "svgolf/README.md", "text": "no such phrase, ever", "with": ""}]
        with self.assertRaises(build.BuildError):
            self.build(config=config)

    def test_a_flow_mismatch_fails_unless_offline(self):
        real = lb.current_flow
        try:
            lb.current_flow = lambda svgolf=None, flow="comb": dict(pinned_flow(flow), yosys=None)   # no Yosys on PATH
            with self.assertRaises(build.BuildError) as e:
                with contextlib.redirect_stderr(io.StringIO()):
                    build.build_site(offline=False)
            self.assertIn("yosys", str(e.exception))
            # the clocked flow is pinned too (`flow_seq`, decided 2026-11-07): a machine whose clocked script differs
            lb.current_flow = lambda svgolf=None, flow="comb": dict(
                pinned_flow(flow), **({"script_sha256": "0" * 64} if flow == "seq" else {}))
            with self.assertRaises(build.BuildError) as e:
                with contextlib.redirect_stderr(io.StringIO()):
                    build.build_site(offline=False)
            self.assertIn("the machine's clocked scoring flow differs from the pin in tests/expected.json (`flow_seq`) "
                          "on script_sha256", str(e.exception))
            lb.current_flow = lambda svgolf=None, flow="comb": dict(pinned_flow(flow))
            with contextlib.redirect_stderr(io.StringIO()):
                build.build_site(offline=False)
        finally:
            lb.current_flow = real

    def test_a_task_without_content_uses_its_readme_and_fails_strict(self):
        real = build.CONTENT
        with tempfile.TemporaryDirectory() as tmp:
            content = os.path.join(tmp, "content")
            shutil.copytree(os.path.join(SITE, "content"), content)
            os.remove(os.path.join(content, "tasks", "add.md"))
            try:
                build.CONTENT = content
                site = self.build()
                self.assertEqual(len(site.warnings), 1)
                self.assertIn("add", site.warnings[0])
                self.assertIn(b"The warm-up challenge", site.files["tasks/add/index.html"])  # the README intro
                with self.assertRaises(build.BuildError):
                    self.build(strict=True)
            finally:
                build.CONTENT = real

    def with_content(self, edit, **kw):
        """Build with a copy of site/content changed by `edit(content_dir)`."""
        real = build.CONTENT
        with tempfile.TemporaryDirectory() as tmp:
            content = os.path.join(tmp, "content")
            shutil.copytree(os.path.join(SITE, "content"), content)
            edit(content)
            try:
                build.CONTENT = content
                return self.build(**kw)
            finally:
                build.CONTENT = real

    def test_an_internal_marker_in_a_curated_text_fails_the_build(self):
        def edit(content):
            path = os.path.join(content, "attacks", "clmul.json")
            with open(path, encoding="utf-8") as fh:
                said = json.load(fh)
            said["negatives"]["drop_top"] += " Found in the round-zz review (QQ-T)."
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(said, fh)
        config = build.load_config()
        config["denylist"] = config["denylist"] + [{"text": t, "scope": "site-text", "why": "a test"}
                                                   for t in ("QQ-", "round-zz")]
        with self.assertRaises(build.BuildError) as e:
            self.with_content(edit, config=config)
        self.assertIn("tasks/clmul/index.html: contains the internal marker 'QQ-'", str(e.exception))
        self.assertIn("'round-zz'", str(e.exception))

    def test_a_missing_curated_sentence_warns_and_fails_strict(self):
        def edit(content):
            path = os.path.join(content, "attacks", "mul.json")
            with open(path, encoding="utf-8") as fh:
                said = json.load(fh)
            del said["negatives"]["drop_carry"]
            said["negatives"]["no_such_design"] = "A design the task does not have."
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(said, fh)
        site = self.with_content(edit)
        self.assertEqual(len(site.warnings), 2, site.warnings)
        self.assertTrue(any("negative drop_carry" in w for w in site.warnings))
        self.assertTrue(any("no_such_design" in w for w in site.warnings))
        page_ = site.files["tasks/mul/index.html"].decode("utf-8")
        self.assertIn("drop_carry.sv", page_)                       # still listed, without a sentence
        self.assertNotIn("refuted in negative", page_)              # never the internal note instead
        with self.assertRaises(build.BuildError):
            self.with_content(edit, strict=True)

    def test_a_design_without_a_proof_is_never_shown_and_fails_strict(self):
        """Decided 2026-11-12: every design the site shows has a kernel-checked proof. Fixtures: a baseline of
        tests/expected.json whose `lean` is dropped, one whose `lean` names a file that is not there, and a design in
        the measured data (score/measured/<task>.json) that is not marked proved. Each is left out of every page and
        data file, with a warning naming it, and the strict build fails."""
        real_read, real_measured = build.read_text, build.metrics.load_measured

        def read_text(rel):
            text = real_read(rel)
            if rel != "svgolf/tests/expected.json":
                return text
            e = json.loads(text)
            del e["tasks"]["add"]["baselines"]["plus"]["lean"]
            e["tasks"]["add"]["baselines"]["cmp_carry"]["lean"] = "baselines/no_such_proof.lean"
            return json.dumps(e)

        def load_measured(name, *a, **kw):
            data = real_measured(name, *a, **kw)
            if name != "clmul" or not data:
                return data
            data = json.loads(json.dumps(data))
            fake = json.loads(json.dumps(next(e for e in data["designs"] if e["name"] == "kara_lv")))
            fake.update(id="baseline/fake_unproved", name="fake_unproved", family="fake_unproved", proved=False)
            fake["sha256"] = "f" * 64
            data["designs"].append(fake)
            return data

        def build_with_fixtures(**kw):
            with mock.patch.object(build, "read_text", read_text), \
                    mock.patch.object(build.metrics, "load_measured", load_measured):
                return self.build(**kw)
        site = build_with_fixtures()
        said = "\n".join(site.warnings)
        for what in ("add: the baseline plus has no proof file (none named)",
                     "add: the baseline cmp_carry has no proof file (svgolf/tests/add/baselines/no_such_proof.lean)",
                     "clmul: the measured design baseline/fake_unproved"):
            self.assertIn(what, said)
        add = site.files["tasks/add/index.html"].decode("utf-8")
        for stem in ("plus", "cmp_carry"):
            self.assertNotIn(f'id="baseline-{stem}"', add)                  # not in the Baselines table
            self.assertNotIn(f"tasks/add/baselines/{stem}.sv", site.files)  # and its file is not offered
            self.assertNotIn(f"baseline/{stem}", add)                       # nor in the charts' data (any point)
        listed = json.loads(site.files["data/tasks/add.json"])["baselines"]           # the published data
        # (2026-11-12) add's other baselines have no banned operator: entries, never baseline lines
        self.assertEqual(sorted(b["stem"] for b in listed), [])
        mul = site.files["tasks/mul/index.html"].decode("utf-8")
        listed = json.loads(site.files["data/tasks/mul.json"])["baselines"]
        self.assertEqual(sorted(b["stem"] for b in listed), ["yosys_mul"])
        for b in listed:
            self.assertTrue(os.path.isfile(build.repo_file(b["lean"])), b)    # each names its proof (either layout)
        self.assertIn('id="baseline-yosys_mul"', mul)                       # a proved baseline is still shown
        self.assertIn("tasks/mul/baselines/yosys_mul.lean", site.files)
        for path in ("tasks/clmul/index.html", "data/tasks/clmul.json"):
            self.assertNotIn("fake_unproved", site.files[path].decode("utf-8"))
        with self.assertRaises(build.BuildError) as e:
            build_with_fixtures(strict=True)
        self.assertIn("has no proof file", str(e.exception))

    def test_internal_markers_spare_verbatim_files_and_player_fields(self):
        deny = ["/nowhere/", {"text": "QQ-", "scope": "site-text"}, {"text": "zz-", "scope": "site-text"}]
        files = {
            "a.html": b'<p>ok</p><pre class="code" data-src="x.sv"><code>// QQ-G note</code></pre>',
            "b.html": b"<p>assisted by ZZ-5 (Example)</p>",
            "c.sv": b"// QQ-G note\n",
            "d.json": b'{"assisted_by": ["ZZ-5 (Example)"]}',
        }
        self.assertEqual(build.check_denylist(files, deny, copies={"c.sv"}, player_text={"ZZ-5 (Example)"}), [])
        hits = build.check_denylist(files, deny, copies=set(), player_text=set())
        self.assertEqual(sorted(h.split(":")[0] for h in hits), ["b.html", "c.sv", "d.json"])
        files["e.html"] = b"<p>see QQ-P</p>"
        hits = build.check_denylist(files, deny, copies={"c.sv"}, player_text={"ZZ-5 (Example)"})
        self.assertEqual(hits, ["e.html: contains the internal marker 'QQ-' (denylist, scope site-text)"])
        files["c.sv"] = b"/nowhere/someone\n"                     # a plain entry: everywhere, copies too
        hits = build.check_denylist(files, deny, copies={"c.sv"}, player_text={"ZZ-5 (Example)"})
        self.assertIn("c.sv: contains the denylisted '/nowhere/'", hits)

    def test_a_stale_marker_allowance_fails_the_build(self):
        config = build.load_config()
        config["denylist"] = config["denylist"] + [{"text": "zz-never-written", "scope": "site-text", "why": "a test",
                                                    "allow": {"about.html": "a test"}}]
        with self.assertRaises(build.BuildError) as e:
            self.build(config=config)
        self.assertIn("about.html: config.json allows the internal marker 'zz-never-written' here", str(e.exception))

    def test_an_all_redaction_replaces_every_occurrence_and_goes_stale_at_zero(self):
        config = build.load_config()
        config["redact"] = config["redact"] + [{"file": "svgolf/README.md", "text": "Yosys", "with": "Yosys", "all": True}]
        self.build(config=config)
        config["redact"][-1]["text"] = "no such phrase, ever"
        with self.assertRaises(build.BuildError) as e:
            self.build(config=config)
        self.assertIn("at least once", str(e.exception))

    def test_the_rules_for_a_record_are_said_in_the_same_words(self):
        """Decided 2026-11-25 (the owner: "You should also put this in the rules the agents read and follow"): the rules
        for a record, build.RECORD_RULES, word for word in README's "The rules for a record" (so on the rules page,
        under its anchor), in CONTRIBUTING and in llms.txt, with the rest of the route (build.NEWER_VERSION_MD); How to
        submit points to them and asks for the writeup as a requirement."""
        config = build.load_config()
        config["repo_url"] = "https://example.org/someone/lean-surfaces.git"
        site = self.build(config=config)
        llms = site.files["llms.txt"].decode("utf-8")
        rules_html = site.files["rules.html"].decode("utf-8")
        self.assertEqual(len(build.RECORD_RULES), 8)       # 2026-11-25 (asap1): both libraries, short notes
        for rel in ("README.md", "CONTRIBUTING.md"):
            with self.subTest(doc=rel):
                text = norm(read_text_file(rel))
                for r in build.RECORD_RULES:
                    self.assertIn(norm(r), text)
                self.assertIn(norm(build.NEWER_VERSION_MD), text)
        for r in build.RECORD_RULES:
            self.assertIn(f"- {r}", llms)
            self.assertIn(norm(r.replace("**", "")), norm(text_of(rules_html)))
        self.assertIn(f"## The rules for a record (the check enforces them; rules.html#{build.RULES_ANCHOR})", llms)
        self.assertIn(build.NEWER_VERSION_MD, llms)
        self.assertIn(f'id="{build.RULES_ANCHOR}"', rules_html)
        part = section(site.files["tasks/clmul/index.html"].decode("utf-8"), "submit")
        self.assertIn(f'rules.html#{build.RULES_ANCHOR}"', part)
        self.assertIn("a record goes in with its writeup, and a writeup never changes the record. It goes in the "
                      "record's pull request (leaderboard.py submit takes it along, and submit and the pull request's "
                      "check refuse a record without one).", norm(text_of(part)))
        self.assertNotIn("still accepted", text_of(part))
        self.assertNotIn("a record without one is still accepted", norm(read_text_file("README.md")))

    def test_submit_with_a_public_repository(self):
        config = build.load_config()
        config["repo_url"] = "https://example.org/someone/lean-surfaces.git"
        site = self.build(config=config)
        page_ = site.files["tasks/clmul/index.html"].decode("utf-8")
        part = text_of(section(page_, "submit"))
        self.assertIn("git clone https://example.org/someone/lean-surfaces.git", part)
        # inside lean-surfaces svGolf is a directory of the clone; standalone it is the clone
        self.assertIn("cd lean-surfaces/svgolf\n" if build.LAYOUT == "inside" else "cd lean-surfaces\n", part)
        self.assertIn("pull request", part)
        self.assertIn("leaderboard/data/clmul/", part)
        self.assertNotIn("Public submissions open when", part)
        self.assertIn("pull request", site.files["llms.txt"].decode("utf-8"))
        self.assertIn("open for submissions", text_of(page_))      # the head's badge, with a public repository
        self.assertNotIn("ready to play", text_of(page_))
        # the record route (decided 2026-11-11), its sentence the same on every page that says how, and this task's
        # submit command; nothing says that CI re-verifies a record, which it never did
        self.assertIn(norm(build.HANDOFF_MD), norm(part))
        # the command that hands the record in: a block with a Copy button (decided 2026-11-12), not inline code
        html_part = section(page_, "submit")
        blocks = [text_of(b) for b in re.findall(r"<pre\b.*?</pre>", html_part, re.S) if "leaderboard.py submit" in b]
        self.assertEqual(len(blocks), 1)
        self.assertEqual([ln.strip() for ln in blocks[0].strip().split("\n")],
                         ["python3.12 leaderboard/leaderboard.py submit --task clmul --record HASH --dry-run",
                          "python3.12 leaderboard/leaderboard.py submit --task clmul --record HASH"])
        self.assertNotIn("<code>python3.12 leaderboard/leaderboard.py submit", html_part)
        self.assertIn("With HASH as step 3 prints it (--dry-run first shows the steps and the pull request's text, and "
                      "changes nothing):", norm(part))
        self.assertIn(build.HANDOFF_MD, site.files["llms.txt"].decode("utf-8"))
        for name in ("about.html", "index.html", "roadmap.html"):
            with self.subTest(page=name):
                text = norm(text_of(site.files[name]))
                self.assertIn(norm(build.HANDOFF_MD), text)
                for other in (build.HANDOFF_UNPUBLISHED_MD, build.HANDOFF_NONE_MD):
                    self.assertNotIn(norm(other), text)
        self.assertIn("Records by pull request", text_of(roadmap_part(site.files["roadmap.html"], "done")))
        self.assertIn("Handing in a record without git", text_of(roadmap_part(site.files["roadmap.html"], "planned")))
        for name, data in site.files.items():
            if name.endswith((".html", ".txt", ".md")):
                self.assertNotIn("CI re-verifies", data.decode("utf-8"), name)

    def test_the_route_is_said_only_where_both_of_its_programs_are(self):
        """"Open for submissions" and the sentence on the pull request need the public repository AND both programs of
        the record route in the tree (decided 2026-11-11): the submit command (leaderboard.py's `submit`) and the
        check of a record's pull request (leaderboard/pr_check.py). Without one of them a page says that a record
        cannot be handed in yet, and the badge says "ready to play"."""
        self.assertTrue(build.route_ready())
        for rel in build.ROUTE_FILES:
            self.assertTrue(os.path.isfile(build.repo_file(rel)), rel)
        missing = build.ROUTE_FILES[:1] + ("svgolf/leaderboard/no_such_check.py",)
        with mock.patch.object(build, "ROUTE_FILES", missing):
            self.assertFalse(build.route_ready())
        with mock.patch.object(build.lb, "cmd_submit", None):
            self.assertFalse(build.route_ready())
        config = build.load_config()
        config["repo_url"] = "https://example.org/someone/svgolf"
        self.assertTrue(build.submissions_open(config))
        self.assertFalse(build.submissions_open(dict(config, repo_url=None)))
        with mock.patch.object(build, "ROUTE_FILES", missing):
            site = self.build(config=config)
        page_ = site.files["tasks/clmul/index.html"].decode("utf-8")
        part = text_of(section(page_, "submit"))
        self.assertIn("ready to play", text_of(page_))
        self.assertNotIn("open for submissions", text_of(page_))
        self.assertIn(norm(build.HANDOFF_NONE_MD), norm(part))
        self.assertNotIn("leaderboard.py submit", part)
        self.assertNotIn("pull request", part)
        llms = site.files["llms.txt"].decode("utf-8")
        self.assertIn(build.HANDOFF_NONE_MD, llms)
        self.assertNotIn("pull request", llms)
        for name in ("about.html", "index.html", "roadmap.html"):
            with self.subTest(page=name):
                text = norm(text_of(site.files[name]))
                self.assertIn(norm(build.HANDOFF_NONE_MD), text)
                self.assertNotIn(norm(build.HANDOFF_MD), text)
        self.assertIn("Records by pull request", text_of(roadmap_part(site.files["roadmap.html"], "planned")))

    def test_strip_sv_comments(self):
        text = ('// header: QQ-G, Someone\n/* block\n   comment */\nmodule m(input a, output y);\n'
                '  assign y = a; // trailing\n\n\n  // only a comment\n  initial $display("// not a comment");\n'
                'endmodule\n// tail\n')
        self.assertEqual(build.strip_sv_comments(text),
                         'module m(input a, output y);\n  assign y = a;\n\n'
                         '  initial $display("// not a comment");\nendmodule\n')



class ReactiveTaskTest(unittest.TestCase):
    """The arbiter (kind react-family), the first clocked task, listing decided 2026-11-07 (directly, no preview). Its
    pages are built alone here (no whole site, no denylist scan: that is the strict build's job): the task page,
    the record pages and any reference page without a record. Clocked wording (decided 2026-11-07): the time is
    the register-to-register period, one decision per cycle, never a critical-path delay or a latency in cycles;
    the golfing loop runs the clocked flow (`--seq`); the Solution.lean skeleton is the reactive reduction's; the
    schematic is the small display instance N = 4 and says so. The reference rr_mask is recorded, so its detail
    page is its record's page, which shows the clocked post-synthesis check (points and seeds) and prices the
    gate mix with the clocked flow's GE table (the flip-flop included)."""

    @classmethod
    def setUpClass(cls):
        site = build.Site(build.load_config())
        refusals = json.loads(site.doc_text(site.config["refusals_json"]))
        site.stages = [s["id"] for s in refusals["svgolf"]["stages"]]
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            tasks = build.collect(site, True)
        cls.t = next(t for t in tasks if t.name == "arbiter")
        build.task_page(site, cls.t)
        ge_tables = build.load_ge_tables()
        for rec in cls.t.records:
            build.record_page(site, cls.t, rec, ge_tables)
        for ref in cls.t.refs:
            if not ref["record_hash"]:
                build.reference_detail_page(site, cls.t, ref, ge_tables)
        cls.site = site
        cls.page = site.files["tasks/arbiter/index.html"].decode("utf-8")
        cls.ref = next(r for r in cls.t.refs if r["stem"] == "rr_mask")
        cls.rec = next((r for r in cls.t.records if r["record_hash"] == cls.ref["record_hash"]), None)
        cls.detail = site.files[f"tasks/arbiter/records/{cls.ref['record_hash']}.html" if cls.ref["record_hash"]
                                else "tasks/arbiter/reference/rr_mask.html"].decode("utf-8")

    def test_the_task_is_listed_and_its_reference_recorded(self):
        self.assertEqual(build.load_config()["tasks"]["arbiter"], "listed")
        self.assertIsNotNone(self.rec, "rr_mask has no record")
        self.assertEqual(self.rec["player"], build.load_config()["reference_player"])
        self.assertEqual(self.rec["checker"]["flow"], "seq")
        self.assertNotIn("preview_note", json.loads(read_text_file("site/content/tasks/arbiter.json")))

    def test_the_pages_build_without_a_warning(self):
        self.assertEqual(self.site.warnings, [])

    def test_the_task_page_speaks_of_the_period(self):
        text = norm(text_of(self.page))
        self.assertIn("clocked, reactive", text)
        self.assertIn("times the register-to-register clock period in ns, one decision per cycle", text)
        # 2026-11-09: the page restates the score nowhere; the Score card (since 2026-11-11 its closed note) is its one
        # definition on the page, and the task text links it
        self.assertNotIn("sky130 µm² times the register-to-register clock period, one decision per cycle", text)
        self.assertNotIn("The score is the area", text)
        for wrong in ("latency in cycles", "critical-path delay", "× 1 ×", "Latency (cycles)", "react-family"):
            self.assertNotIn(wrong, text)
        self.assertIn("N in range 1 <= N, N*N < 2^31", text)              # the "At a glance" card
        at = text.index("banned run-time operators")
        self.assertTrue(text[at:at + 40].replace(" ", "").startswith("bannedrun-timeoperators/%**"), text[at:at + 40])

    def test_how_to_submit_uses_the_clocked_flow_and_the_reactive_skeleton(self):
        """2026-11-09: the golfing loop and the reactive skeleton are on the page once: the golfing loop is How to
        submit's first command (since 2026-11-11; the card's own, with the clocked flow), the skeleton the README's in
        "Proving a new design" (folded), which How to submit points to; the skeleton How to submit shows on a page
        without a card is still the reactive reduction's."""
        part = text_of(section(self.page, "submit"))
        card = text_of(section(self.page, "new-design"))
        self.assertIn("--seq --path", part)
        self.assertNotIn("--seq --path", card)
        for text in (part, card):
            self.assertNotIn("--no-mapped", text)
            self.assertNotIn("SvGolf.Comb", text)
        self.assertIn("import SvGolf.React", card)
        self.assertIn("satisfiedAt_of_rank", card)
        self.assertIn(f'href="#{build.NEW_DESIGN_FOLD}"', section(self.page, "submit"))
        skeleton = build.solution_skeleton(self.t)
        self.assertIn("import SvGolf.React", skeleton)
        self.assertIn("satisfiedAt_of_rank", skeleton)
        self.assertNotIn("SvGolf.Comb", skeleton)
        self.assertIn(f'href="../../proving.html#{build.REACT_SECTION}"', section(self.page, "new-design"))
        proving = read_text_file("PROVING.md")
        self.assertEqual(build.md.Slugger().slug(re.search(r"^## (20\. .+)$", proving, re.M).group(1)),
                         build.REACT_SECTION)

    def test_the_new_design_card_names_the_reactive_route(self):
        card = norm(text_of(section(self.page, "new-design")))
        for word in build.NEW_DESIGN_ROUTE["react-family"]:
            self.assertIn(word, card)
        self.assertNotIn("--tactics solution", card)

    def test_the_detail_page_draws_the_display_instance_and_reads_a_clocked_path(self):
        text = norm(text_of(self.detail))
        self.assertIn("Drawn at N = 4; scored at N = 8. why? This is a display instance.", text)   # (2026-11-16)
        self.assertIn("The register-to-register critical path at N = 4", text)
        self.assertIn("the register-to-register period, one decision per cycle", text)
        self.assertIn("The path the ranked register-to-register period ends on", text)
        self.assertIn("to the flip-flop input _009_ falling", text)
        self.assertIn("The first row is a flip-flop's Q", text)
        self.assertNotIn("The first row is an input", text)
        self.assertNotIn("1 cycles", text)

    def test_the_task_page_says_when_a_grant_comes_and_what_is_banned(self):
        """The task's own text (content/tasks/arbiter.md) states the range, the ban, the clocking and the timing of
        a grant (a Moore output: one cycle after its request). The period, one decision per cycle, is the Score
        card's (test_the_task_page_speaks_of_the_period), which the text links (2026-11-09: the score defined once)."""
        text = norm(text_of(self.page))
        statement = norm(text_of(section(self.page, "statement")))
        for phrase in ("every N with 1 <= N, N*N < 2^31", "Run-time / % ** are banned",
                       "a Moore output: a clock edge samples req", "a grant follows its request by one cycle",
                       "The design is clocked by clk alone, on its rising edge, with the synchronous reset rst",
                       "so the task is the policy and its state, which the score prices"):
            self.assertIn(phrase, statement)
        self.assertIn("times the register-to-register clock period in ns, one decision per cycle", text)

    def test_the_record_page_shows_the_clocked_post_synthesis_check(self):
        """A clocked record's `postsynth` has no `vectors`, `point` or `seed`: the card shows its points, seeds,
        cycles and mismatches instead, and every seed's draw (leaderboard/README.md, `postsynth`)."""
        card = section(self.detail, "postsynth")
        part = norm(text_of(card))
        rows = table_rows(card)
        ps = self.rec["postsynth"]
        self.assertNotIn("None", part)
        self.assertNotIn("vectors", part)
        self.assertNotIn("latency", part)                       # one decision per cycle: no latency column
        self.assertIn("N = 3, N = 5, N = 8 (the scoring point)", part)
        self.assertIn("8 seeds per point: seed 0 from the all-zeros power-up", part)
        self.assertIn("24 segments per seed", part)
        self.assertIn("the Moore sample", part)
        self.assertIn("The check found no mismatch.", part)
        self.assertIn("no (the default empty salt", part)
        self.assertIn(ps["netlist_sha256"], part)
        total = sum(sd["cycles"] for pt in ps["points"] for sd in pt["seeds"])
        self.assertIn(norm(f"{build.thin(total)} in all"), part)
        for pt in ps["points"]:
            with self.subTest(point=pt["point"]):
                name = norm(build.point_text(pt["params"]))
                self.assertIn([name, "8", norm(build.thin(sum(sd["cycles"] for sd in pt["seeds"]))),
                               str(sum(sd["segments"] for sd in pt["seeds"])), "0", pt["netlist_sha256"][:12]], rows)
                for sd in pt["seeds"]:
                    self.assertIn([name, str(sd["seed"]), sd["lssv_start"], str(sd["netlist_randseed"]),
                                   norm(build.thin(sd["cycles"])), str(sd["segments"]), sd["seed_sha256"][:12]], rows)
        self.assertIn("every seed's run (24)", part)

    def test_the_record_page_reproduces_through_the_clocked_flow(self):
        """The record page's "Reproduce and verify" command is the clocked flow's (`ppa.py --seq`, as the record
        was weighed; without it the comb flow refuses the netlist's flip-flops), and the values it says to expect
        are the record's own five: the RTLIL, the scored and the repaired netlist, the area and the period."""
        part = text_of(section(self.detail, "reproduce"))
        self.assertIn("python3.12 score/ppa.py tasks/arbiter/reference/rr_mask.sv --task tasks/arbiter --seq --path",
                      part)
        self.assertIn("--json out.json --netlist scored.v --repaired-netlist repaired.v", part)
        p = self.rec["ppa"]
        for key, value in (("score.rtlil_sha256", self.rec["score"]["rtlil_sha256"]),
                           ("ppa.netlist_sha256", p["netlist_sha256"]),
                           ("ppa.repair.netlist_sha256", p["repair"]["netlist_sha256"]),
                           ("ppa.area_e4um2_sky130", str(p["area_e4um2_sky130"])),
                           ("ppa.delay_ps_sky130", str(p["delay_ps_sky130"]))):
            with self.subTest(key=key):
                self.assertIn(key + value, part.replace(" ", "").replace("\n", ""))

    def test_the_gate_mix_prices_the_flip_flops(self):
        """The extra GE column of a clocked record comes from score/ge_seq.json (the flip-flop priced): its rows
        add up to the record's area_ge, the DFF_P row included."""
        card = section(self.detail, "cells")
        self.assertIn("score/ge_seq.json", norm(text_of(card)))
        ge_seq = json.loads(build.read_text("svgolf/score/ge_seq.json"))
        n = self.rec["score"]["gates"]["DFF_P"]
        self.assertIn(["DFF_P", str(n), f"{ge_seq['DFF_P']:.3f}", build.lb.fmt_ge(round(ge_seq["DFF_P"] * 1000) * n)],
                      table_rows(card))
        self.assertEqual(sum(round(ge_seq[g] * 1000) * k for g, k in self.rec["score"]["gates"].items()),
                         self.rec["score"]["area_mge"])

    def test_the_factors_and_the_metrics_follow_the_kind(self):
        d = {"m": {"area_um2": 769.488, "time_ps": 2826, "cycles": 1, "period_ps": 2826}}
        self.assertEqual(build.breakdown(d, self.t), "769.5 µm² × 2.83 ns")

        class Tx:
            task = {"kind": "tx-family"}
        self.assertEqual(build.breakdown(d, Tx), "769.5 µm² × 1 × 2.83 ns")
        self.assertEqual(build.breakdown(d), "769.5 µm² × 1 × 2.83 ns")
        # the page head's labelled form: one cycle is singular (a latency-1 record, matmul's four-step design)
        self.assertEqual(build.breakdown(d, Tx, labels=True), "769.5 µm² × 1 cycle × 2.83 ns period")
        d4 = {"m": dict(d["m"], cycles=4, time_ps=4 * 2826)}
        self.assertEqual(build.breakdown(d4, Tx, labels=True), "769.5 µm² × 4 cycles × 2.83 ns period")
        keys = [m.key for m in build.metric_table(self.t)]
        self.assertIn("time_ps", keys)
        self.assertNotIn("cycles", keys)
        self.assertNotIn("period_ps", keys)
        self.assertIn("cycles", [m.key for m in build.metric_table(Tx)])


class LatencyTaskTest(unittest.TestCase):
    """matmul (kind tx-family) and the sorter (stream-family), the clocked tasks with a latency, listed and ranked
    as decided 2026-11-08 (before, they were unranked previews). Their pages are built alone here, as ReactiveTaskTest
    builds the arbiter's. Clocked wording: the time is the latency in cycles times the register-to-register period;
    the golfing loop runs the clocked flow (`--seq`); the Solution.lean skeleton carries the header line
    `-- svgolf-latency: n`, the latency definition `lat` and the goal `Goal lat`, with par's pair as the example, and
    check.py reads its header as par's latency; the "Proving a new design" card names the v2 phase route; the
    schematic is a small display instance and says so."""

    TASKS = {"matmul": ("tx-family", "clocked, transaction", "TxTask.satisfiedAtV2_of_phases"),
             "sorter": ("stream-family", "clocked, stream", "StreamTask.satisfiedAtV2_of_phases")}

    @classmethod
    def setUpClass(cls):
        site = build.Site(build.load_config())
        refusals = json.loads(site.doc_text(site.config["refusals_json"]))
        site.stages = [s["id"] for s in refusals["svgolf"]["stages"]]
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            tasks = build.collect(site, True)
        cls.t = {t.name: t for t in tasks if t.name in cls.TASKS}
        cls.numbers = {t.name: t.number for t in tasks}
        ge_tables = build.load_ge_tables()
        for t in cls.t.values():
            build.task_page(site, t)
            for rec in t.records:
                build.record_page(site, t, rec, ge_tables)
            for ref in t.refs:
                if not ref["record_hash"]:
                    build.reference_detail_page(site, t, ref, ge_tables)
        build.rules_page(site, refusals, tasks)             # "The time, and the clock period" (since 2026-11-11)
        cls.site = site
        cls.page = {n: site.files[f"tasks/{n}/index.html"].decode("utf-8") for n in cls.t}
        cls.rules = site.files["rules.html"].decode("utf-8")
        spec = importlib.util.spec_from_file_location("svgolf_check_py_latency", os.path.join(SVGOLF, "check.py"))
        cls.checkpy = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.checkpy)

    def detail(self, name):
        """The detail page of the task's par: its record's page when recorded, else its reference page."""
        ref = self.t[name].par
        path = (f"tasks/{name}/records/{ref['record_hash']}.html" if ref["record_hash"]
                else f"tasks/{name}/reference/{ref['stem']}.html")
        return self.site.files[path].decode("utf-8")

    def test_the_tasks_are_listed_with_their_kinds(self):
        config = build.load_config()
        self.assertEqual(set(self.t), set(self.TASKS))
        for name, (kind, _, _) in self.TASKS.items():
            with self.subTest(task=name):
                self.assertEqual(config["tasks"][name], "listed")
                self.assertEqual(self.t[name].kind, kind)
                self.assertIsNotNone(self.t[name].par)
                self.assertNotIn("preview_note", json.loads(read_text_file(f"site/content/tasks/{name}.json")))
                self.assertGreaterEqual(len(self.t[name].views), 2)              # the measured points
        # listed after the arbiter, which keeps the number it was published with
        self.assertEqual((self.numbers["arbiter"], self.numbers["matmul"], self.numbers["sorter"]), ("06", "07", "08"))

    def test_the_pages_build_without_a_warning(self):
        self.assertEqual(self.site.warnings, [])

    def test_the_task_page_speaks_of_the_latency(self):
        for name, (kind, short, _) in self.TASKS.items():
            with self.subTest(task=name):
                text = norm(text_of(self.page[name]))
                self.assertIn(short, text)
                self.assertIn("times the latency in cycles × the register-to-register clock period in ns", text)
                for wrong in ("one decision per cycle", "critical-path delay", kind, "preview", "Not ranked yet"):
                    self.assertNotIn(wrong, text)
                for big in ("Par", "Record", "Under par"):
                    self.assertIn(big, text_of(section(self.page[name], "numbers")))
                at = text.index("banned run-time operators")
                self.assertTrue(text[at:at + 40].replace(" ", "").startswith("bannedrun-timeoperators/%**"),
                                text[at:at + 40])

    def test_how_to_submit_uses_the_clocked_flow_and_the_latency_skeleton(self):
        proving = read_text_file("PROVING.md")
        anchor = build.md.Slugger().slug(re.search(rf"^## ({build.SEQ_SECTION_NO}\. .+)$", proving, re.M).group(1))
        for name, (kind, _, reduction) in self.TASKS.items():
            with self.subTest(task=name):
                t = self.t[name]
                part = text_of(section(self.page[name], "submit"))
                card = text_of(section(self.page[name], "new-design"))
                # 2026-11-09: the golfing loop, the --unproved run and the skeleton are the "Proving a new design"
                # card's (the README's), once on the page: since 2026-11-11 the two commands are How to submit's first
                # two, the skeleton is in the card (How to submit's last part); the generated skeleton below is what
                # How to submit shows on a page without a card
                skeleton = build.solution_skeleton(t)
                self.assertNotIn(skeleton, part)
                self.assertIn("--seq --path", part.replace(" \\\n    ", " "))
                self.assertNotIn("--seq --path", card)
                for text in (part, card):
                    self.assertNotIn("--no-mapped", text)
                    self.assertNotIn("SvGolf.Comb", text)
                # the header line is check.py's, and its number is par's latency at the scoring point
                par_lean = build.read_text(t.par["lean"])
                n = self.checkpy.parse_latency(par_lean, kind)
                self.assertEqual(self.checkpy.parse_latency(skeleton, kind), n)
                self.assertIn(f"-- svgolf-latency: {n}\n", skeleton)
                # the --unproved run claims par's latency: check.py refuses it without --latency; so does the card's
                # skeleton's header line; How to submit's comment says the number is par's
                self.assertIn(f"python3.12 check.py tasks/{name} solution.sv --unproved --latency {n} ",
                              part.replace(" \\\n    ", " "))
                self.assertIn(f"--latency: the cycles you mean to claim ({n}: par's)", part)
                self.assertIn(f"-- svgolf-latency: {n}\n", card)
                self.assertEqual(build.unproved_latency(t), str(n))
                self.assertIn(f"python3.12 check.py tasks/{name} solution.sv --unproved \\\n    --latency {n}\n",
                              build.submit_commands(t))
                lat_def = next(ln for ln in par_lean.split("\n") if ln.startswith("def lat "))
                self.assertIn(lat_def + "\n", skeleton)
                for phrase in ("import SvGolf.SeqV2", "theorem solution : Goal lat := by",
                               "`theorem Submission.solution : Submission.Goal Submission.lat`",
                               "refine ⟨fun p hp => ?_, rfl⟩", reduction, "combDeps_of_ffOnly", "XSafe",
                               f"tasks/{name}/reference/{t.par['stem']}.lean"):
                    self.assertIn(phrase, skeleton)
                p0 = " ".join(str(t.point[p["name"]]) for p in t.task["parameters"])
                self.assertIn(f"{t.task['statement']['constant']} Submission.design.sem lat ∧ lat {p0} = n", part)
                self.assertIn("exactly one line -- svgolf-latency: n", part)
                self.assertIn("theorem Submission.solution : Submission.Goal Submission.lat", part)
                self.assertIn(f'href="../../proving.html#{anchor}"', section(self.page[name], "new-design"))

    def test_the_new_design_card_names_the_phase_route(self):
        for name, (kind, _, _) in self.TASKS.items():
            with self.subTest(task=name):
                card = norm(text_of(section(self.page[name], "new-design")))
                for word in build.NEW_DESIGN_ROUTE[kind]:
                    self.assertIn(word, card)
                self.assertNotIn("--tactics solution", card)
                # the closed-form clock step is FF-only (FFOnly: every process an always_ff with a nonblocking-only
                # body); a comb process means proving the settle, as the arbiter's proof does (PROVING.md s20)
                for phrase in ("keep every process an always_ff whose body writes with nonblocking assignments only",
                               "cycleStep2_ffOnly", "A continuous assign or an always_comb block anywhere",
                               "proving the combinational settle yourself", "PROVING.md, section 20"):
                    self.assertIn(phrase, card)
        # the extractor refuses a widened $signed (ConversionExpression:width); the reference sign-extends by hand
        card = norm(text_of(section(self.page["matmul"], "new-design")))
        self.assertIn("ConversionExpression:width", card)
        self.assertIn("{{AccW{x[W-1]}}, x}", card)
        self.assertIn("{{AccW{a_sh[i*N*W + W - 1]}}, a_sh[i*N*W +: W]}", build.read_text(self.t["matmul"].par["sv"]))
        # the card's opening is the README's (the page shows its last sentence only: each task fact once)
        self.assertIn("A new matrix multiplier is your own `solution.sv`", read_text_file("tasks/matmul/README.md"))
        self.assertNotIn("A new matrix multiplier is your own solution.sv", card)

    def test_the_score_caption_counts_the_input_and_output_paths(self):
        """score/ppa.py's clocked STA: paths start at the inputs and at every Q and end at the outputs and at every D,
        so the period is not register-to-register alone; the rules page's "The time, and the clock period" says so
        (since 2026-11-11 the task page's score card links it in place of its long caption)."""
        ppa_src = norm(read_text_file("score/ppa.py"))          # the ASAP7 port wrapped the sentence anew
        self.assertIn("Paths start at the inputs and at every", ppa_src)
        self.assertIn("and end at the outputs", ppa_src)
        period = norm(text_of(self.rules.split('id="clock-period"', 1)[1].split("<h3", 1)[0]))
        self.assertIn("so paths from the inputs and to the outputs count too", period)
        self.assertIn("The clock period (what score/ppa.py calls the register-to-register period) is the longest path",
                      period)
        for name in self.TASKS:
            with self.subTest(task=name):                   # the score card's note links it, by the clock's name
                self.assertIn('href="../../rules.html#clock-period">the clock period</a>',
                              section(self.page[name], "score"))

    def test_the_files_card_says_a_copy_of_a_licensed_reference_keeps_its_notice(self):
        files = {n: norm(text_of(self.page[n].split('id="files"', 1)[1].split('id="explore"', 1)[0]))
                 for n in self.TASKS}
        self.assertIn("sorter_ins.sv is adapted from licensed code (MIT): a design derived from it keeps the copyright "
                      "and licence notices of its header.", files["sorter"])
        self.assertNotIn("licensed code", files["matmul"])

    def test_the_detail_page_draws_the_display_instance_and_prices_the_cycles(self):
        display = json.loads(read_text_file("site/schematics/display.json"))["tasks"]
        for name in self.TASKS:
            with self.subTest(task=name):
                t = self.t[name]
                text = norm(text_of(self.detail(name)))
                small, scored = build.point_text(display[name]["params"]), build.point_text(t.point)
                self.assertIn(f"Drawn at {small}; scored at {scored}. why? This is a display instance.", text)
                self.assertIn(f"The register-to-register critical path at {small}", text)
                m = build.par_design(t)["m"]
                # score/ppa.py's clocked STA ends its paths at the outputs and at every D (arrival + setup)
                self.assertIn(norm(f"{m['cycles']} cycles × {build.thin(m['period_ps'])} ps; the period is the latest "
                                   "arrival at an output, or at a flip-flop's D plus setup, ideal clock"), text)
                self.assertNotIn("the latest D arrival plus setup", text)
                self.assertEqual(m["time_ps"], m["cycles"] * m["period_ps"])
                self.assertNotIn("one decision per cycle", text)
                self.assertNotIn("not computed yet", text)
                self.assertNotIn("stale:", text)

    def test_the_record_page_shows_the_latency_of_each_point(self):
        """F8: a latency kind checks each post-synthesis point against its own latency, the solution's `lat` there
        (the record's `latency` per point, from check.py's `latency_at`); the post-synthesis card's table shows it,
        beside the point."""
        for name in self.TASKS:
            with self.subTest(task=name):
                t = self.t[name]
                self.assertTrue(t.par["record_hash"])
                rec = next(r for r in t.records if r["record_hash"] == t.par["record_hash"])
                card = section(self.detail(name), "postsynth")
                rows = table_rows(card)
                self.assertIn(["point", "latency (cycles)", "seeds", "clock cycles", "transactions", "mismatches",
                               "netlist sha256"], rows)
                self.assertIn("Each point ran against its own latency, the solution's lat at that point",
                              norm(text_of(card)))
                points = rec["postsynth"]["points"]
                self.assertGreaterEqual(len({pt["latency"] for pt in points}), 2)     # the points differ (F8)
                for pt in points:
                    self.assertIn([norm(build.point_text(pt["params"])), str(pt["latency"]), str(len(pt["seeds"]))],
                                  [r[:3] for r in rows])

    def test_the_mit_reference_says_it_is_adapted_from_licensed_code(self):
        """The sorter's reference carries the MIT notice of andrewpeck/cell-sort in full, with no SPDX identifier: its
        sources card says it is adapted from licensed code, as an SPDX-marked design's does; matmul's own code does
        not. A notice counts only in full (the MIT grant without its condition is MIT-0's)."""
        sources = {n: norm(text_of(section(self.detail(n), "sources"))) for n in self.TASKS}
        self.assertNotIn("SPDX-License-Identifier", build.read_text(self.t["sorter"].par["sv"]))
        self.assertIn("Adapted from licensed code (MIT): the copyright, provenance and licence notices and the list "
                      "of changes are kept in the design file, shown in full below.", sources["sorter"])
        self.assertNotIn("Adapted from licensed code", sources["matmul"])
        # a player's design that keeps the notice: its card claims the notice only, not a list of changes
        refp = build.load_config()["reference_player"]
        players = [r for _, r, _ in build.lb.load_records(build.repo_file("svgolf/leaderboard/data"), "sorter")
                   if r and r.get("player") != refp]
        checked = 0
        for r in players:
            sv = build.read_text(f"svgolf/leaderboard/data/sorter/{r['record_hash']}.sv")
            if build.licence_ids(sv):
                checked += 1
                page_text = self.site.files[f"tasks/sorter/records/{r['record_hash']}.html"].decode("utf-8")
                card = norm(text_of(section(page_text, "sources")))
                self.assertIn("Adapted from licensed code (MIT): its licence notice is in the design file, shown in "
                              "full below.", card)
                self.assertNotIn("the list of changes", card)
        self.assertGreaterEqual(checked, 1)     # kestrel-golf's 999504da3683 keeps the reference's MIT notice
        grant, condition = build.LICENCE_NOTICES["MIT"]
        self.assertEqual(build.licence_ids(f"// {grant[:60]}\n//   {grant[60:]}\n/* {condition} */\n"), ["MIT"])
        self.assertEqual(build.licence_ids(f"// {grant}\n"), [])
        self.assertEqual(build.licence_ids(f"// SPDX-License-Identifier: Apache-2.0\n// {grant} {condition}\n"),
                         ["Apache-2.0", "MIT"])

if __name__ == "__main__":
    unittest.main()
