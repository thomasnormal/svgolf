"""The writeups on the site (decided 2026-11-13, the owner's UI feedback items 3 and 6; HTML since 2026-11-16):
site/writeup.py renders a player's HTML from site/safehtml.py's checked tree (the allowlists, refusals naming the
line: tests/site/test_safehtml.py is the adversarial battery), links to http(s) addresses carry rel="nofollow ugc
noopener", headings sit under the card with ids that cannot take one of the page's; the record page shows the
writeup as a card, its title as the page's heading, the title in the submissions list and the charts' tooltips; a
record without one shows a short prompt.

    python3.12 svgolf/tests/site/test_writeup.py

Hostile input is fed to the renderer directly; the site-level checks build the site once (--offline)."""

import contextlib
import html
import io
import os
import re
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
SITE = os.path.join(SVGOLF, "site")
sys.path.insert(0, SITE)
sys.path.insert(0, HERE)

import safehtml    # noqa: E402
import writeup     # noqa: E402


def render(body, title="T"):
    return writeup.render(f"<h1>{title}</h1>\n\n{body}\n", source="w.html")[1]


def tags(h):
    """The tag names the HTML opens."""
    return sorted(set(re.findall(r"<([a-zA-Z][a-zA-Z0-9]*)", h)))


ALLOWED_TAGS = {"a", "code", "em", "h3", "h4", "h5", "li", "ol", "p", "pre", "span", "strong", "table", "tbody",
                "td", "th", "thead", "tr", "ul", "div", "hr", "br", "sub", "sup", "blockquote"}


class RendererTest(unittest.TestCase):
    def test_hostile_html_is_refused_and_escaped_text_stays_text(self):
        for body in ("<script>alert(1)</script>", "<p><img src=x onerror=alert(1)></p>",
                     "<p><a href='javascript:x'>a</a></p>", "<iframe src=https://evil.example></iframe>",
                     "<style>body{display:none}</style>", "<p><svg onload=alert(1)></svg></p>",
                     "<!-- comment --> <p><b>bold</b></p>", "<p>&lt;script&gt; & <<x>></p>"):
            with self.subTest(body=body):
                with self.assertRaises(safehtml.HtmlError):
                    render(body)
        h = render("<p>&lt;script&gt;alert(1)&lt;/script&gt; &amp; a &lt; b &gt; c \"q\" 'a'</p>")
        self.assertEqual(h, "<p>&lt;script&gt;alert(1)&lt;/script&gt; &amp; a &lt; b &gt; c \"q\" 'a'</p>")
        self.assertLessEqual(set(tags(h)), ALLOWED_TAGS)

    def test_relative_links_go_through_the_site_resolver(self):
        """Decided 2026-11-23 (a writeup links the designs it names, and shows a record submitted after its own only as
        "on the board since <date>"): with the site build's `resolve_link`, a link to a later record carries
        writeup.BOARD_SINCE and the words follow it; a repository file the site cannot link yet is a span.unlinked
        naming it (md.py's form); a link the resolver refuses fails the writeup at its line; mailto, #id and http(s)
        links never reach the resolver; without one (leaderboard.py verify) a relative path is kept."""
        seen = []

        def resolve(href):
            seen.append(href)
            if href == "gone.html":
                raise ValueError("names no record's page")
            if href == "../reference/x.sv":
                return writeup.Link(None, title="tasks/t/reference/x.sv")
            return writeup.Link(href, later="2026-11-13" if href == "later.html" else None)

        def r(body):
            return writeup.render(f"<h1>T</h1>\n\n<h2>H</h2>\n{body}\n", source="w.html", resolve_link=resolve)[1]
        h = r('<p>As <a href="later.html">its record</a>, after <a href="earlier.html">that one</a>.</p>')
        self.assertIn('<p>As <a class="board-since" href="later.html">its record</a> (on the board since 2026-11-13), '
                      'after <a href="earlier.html">that one</a>.</p>', h)
        self.assertIn('<p><span class="unlinked" title="tasks/t/reference/x.sv"><code>x</code></span></p>',
                      r('<p><a href="../reference/x.sv"><code>x</code></a></p>'))
        with self.assertRaises(safehtml.HtmlError) as e:
            r('<p>a</p>\n<p><a href="gone.html">g</a></p>')
        self.assertIn("names no record's page", str(e.exception))
        seen.clear()
        r('<p><a href="https://example.org/">a</a> <a href="mailto:a&#64;example.org">b</a> <a href="#h">c</a></p>')
        self.assertEqual(seen, [])
        self.assertIn('<a href="later.html">x</a>', render('<p><a href="later.html">x</a></p>'))

    def test_only_safe_links_are_links(self):
        h = render('<p><a href="https://example.org/x?y=1&amp;z=2#z">a</a> <a href="http://example.org">b</a></p>')
        self.assertIn('<a rel="nofollow ugc noopener" href="https://example.org/x?y=1&amp;z=2#z">a</a>', h)
        self.assertIn('<a rel="nofollow ugc noopener" href="http://example.org">b</a>', h)
        # a relative path to a page of the site, a mailto address and a fragment of this writeup are kept
        # (the address written with a character reference, as an author may; the site writes the character)
        h = render('<h2>The idea</h2>\n<p><a href="../index.html">t</a> <a href="mailto:a&#64;example.org">m</a> '
                   '<a href="#the-idea">i</a></p>')
        self.assertIn('<a href="../index.html">t</a> <a href="mailto:a' + chr(64) + 'example.org">m</a> '
                      '<a href="#writeup-the-idea">i</a>', h)
        for target in ("javascript:alert(1)", "JAVASCRIPT:alert(1)", "data:text/html,<script>x</script>",
                       "vbscript:x", "//evil.example/x", "/abs", "file:///etc/passwd", "https:///nohost",
                       'https://ex"onmouseover=alert(1)', "https://example.org/`x`", "https://user@localhost/",
                       "mailto:someone", "#nothing-here", "#schematics", " https://example.org", "HTTPS://x.org"):
            with self.subTest(target=target):
                with self.assertRaises(safehtml.HtmlError):
                    render(f"<p><a href=\"{html.escape(target)}\">click</a></p>")

    def test_code_is_escaped_and_highlighted_by_the_site(self):
        h = render('<pre><code class="language-lean">&lt;/code&gt;&lt;/pre&gt;&lt;script&gt;x</code></pre>\n\n'
                   "<p><code>&lt;/code&gt;&lt;b&gt;x&lt;/b&gt;</code></p>")
        self.assertNotIn("<script", h)
        self.assertNotIn("<b>", h)
        self.assertIn('<pre class="code" data-lang="lean"><code>&lt;/code&gt;&lt;/pre&gt;&lt;script&gt;x</code>'
                      "</pre>", h)
        seen = []
        writeup.render('<h1>T</h1>\n\n<pre><code class="language-sv">a</code></pre>\n', source="w",
                       highlight=lambda code, lang: seen.append((code, lang)) or "X")
        self.assertEqual(seen, [("a", "sv")])

    def test_headings_start_under_the_card_and_never_take_a_page_id(self):
        h = render("<h2>Sources</h2>\n\n<h3>main</h3>\n\n<h4>netlist</h4>")
        self.assertNotIn("<h1", h)
        self.assertNotIn("<h2", h)
        ids = re.findall(r'\bid="([^"]+)"', h)
        self.assertEqual(ids, ["writeup-sources", "writeup-main", "writeup-netlist"])
        self.assertIn('<h3 id="writeup-sources">Sources <a class="anchor" href="#writeup-sources" aria-label="link to '
                      'this section">#</a></h3>', h)
        self.assertIn('<h4 id="writeup-main">', h)
        self.assertIn('<h5 id="writeup-netlist">', h)
        with self.assertRaises(safehtml.HtmlError):
            render('<h2 id="schematics">x</h2>')                         # ids are the site's

    def test_the_title_is_plain_text(self):
        title, _ = writeup.render("<h1>&lt;b&gt;Bold&lt;/b&gt; &amp; `code`</h1>\n\n<p>body</p>\n", source="w.html")
        self.assertEqual(title, "<b>Bold</b> & `code`")          # the caller escapes it
        for bad in ("No title\n\n<p>body</p>\n", "# Markdown\n\n<p>body</p>\n", "<h1><em>x</em></h1>\n"):
            with self.assertRaises(ValueError):
                writeup.render(bad, source="w.html")
        self.assertEqual(writeup.fallback_title("mul_tree.sv"), "mul_tree")

    def test_safe_target(self):
        self.assertEqual(writeup.safe_target("https://a.example/b"), "https://a.example/b")
        for bad in (None, "", "http:/x", "https://a b", "https://a.example/\x00", "https://a.example/<x>"):
            self.assertIsNone(writeup.safe_target(bad), bad)


class SiteWriteupTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import importlib.util
        spec = importlib.util.spec_from_file_location("svgolf_site_build_w", os.path.join(SITE, "build.py"))
        cls.build = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.build)
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            cls.site = cls.build.build_site(offline=True)
        cls.lb = cls.build.lb
        cls.recs = [r for _, r, _ in cls.lb.load_records(cls.lb.DEFAULT_DATA)]

    def page(self, rec):
        return self.site.files[f"tasks/{rec['task']}/records/{rec['record_hash']}.html"].decode("utf-8")

    def test_a_writeup_is_the_record_pages_card_and_heading(self):
        seen = 0
        for rec in self.recs:
            path = os.path.join(self.lb.WRITEUPS_DIR, rec["record_hash"] + ".html")
            h = self.page(rec)
            with self.subTest(record=rec["record_hash"][:12]):
                # the page's Writeup tab (decided 2026-11-16): its pane holds the id, the card or the one-line prompt
                pane = re.search(r'<section class="tabs-pane" id="writeup"><h2 class="tabs-pane-title">Writeup</h2>'
                                 r'(.*?)</section>(?=<section class="tabs-pane" id="schematics">)', h, re.S)
                self.assertIsNotNone(pane)
                card = (re.match(r'<section class="card writeup">(.*)$', pane.group(1), re.S)
                        or re.match(r'<p class="empty writeup-none">(.*)</p>$', pane.group(1), re.S))
                self.assertIsNotNone(card)
                self.assertEqual(h.count('id="writeup"'), 1)
                h1 = re.search(r"<h1\b[^>]*>(.*?)</h1>", h, re.S).group(1)
                if os.path.isfile(path):
                    with open(path, encoding="utf-8") as fh:
                        title = self.lb.writeup_title(fh.read())
                    self.assertEqual(h1, html.escape(title))
                    self.assertIn("The writeup", card.group(1))
                    self.assertIn("Writeup by the maintainers, from the design and proof files.", card.group(1))
                    seen += 1
                else:
                    self.assertIn("No writeup yet", card.group(1))
                    self.assertIn('rules.html#writeups"', card.group(1))
        self.assertGreater(seen, 30)

    def test_a_record_without_a_writeup_shows_the_prompt(self):
        rec = self.recs[0]
        saved = self.site.writeups.pop(rec["record_hash"], None)
        try:
            out = self.build.writeup_card(self.site, f"tasks/{rec['task']}/records/x.html", rec)
        finally:
            if saved:
                self.site.writeups[rec["record_hash"]] = saved
        self.assertIn("No writeup yet", out)
        self.assertIn("How to add a writeup", out)
        # one line (decided 2026-11-16, the Writeup tab): the site's empty box, no card, no title of its own
        self.assertRegex(out, r'^<p class="empty writeup-none">[^<]*<a href="[^"]*rules\.html#writeups">How to add a '
                              r'writeup</a>\.</p>$')
        self.assertEqual(self.build.record_title(type("S", (), {"writeups": {}})(), rec),
                         writeup.fallback_title(rec["files"]["sv"]["name"]))

    def test_the_title_is_in_the_submissions_list_and_the_tooltips(self):
        for t in ("mul", "matmul", "add"):
            with self.subTest(task=t):
                h = self.site.files[f"tasks/{t}/index.html"].decode("utf-8")
                board = h.split('id="leaderboard"', 1)[1].split("</ol>", 1)[0]
                for rec in (r for r in self.recs if r["task"] == t and r["player"] != "svgolf-reference"):
                    title = self.build.record_title(self.site, rec)
                    self.assertIn(f'<span class="board-title">{html.escape(title)}</span>', board)
                    # the score chart's mark of the record names the title first in its tooltip
                    self.assertRegex(h, r'data-id="' + rec["record_hash"] + r'"[^>]*data-tip="'
                                     + re.escape(html.escape(title)) + "\n")

    def test_every_page_runs_only_the_sites_own_scripts(self):
        """Defence in depth behind the writeups' sanitizer (decided 2026-11-16): every page carries the site's
        Content-Security-Policy (page.py CSP) as its first <meta> after the charset, and holds no inline script (a
        JSON data block is no script), no event-handler attribute and no javascript: address."""
        import html.parser
        import page

        class Scan(html.parser.HTMLParser):
            def __init__(self):
                super().__init__(convert_charrefs=True)
                self.bad = []

            def handle_starttag(self, tag, attrs):
                a = dict(attrs)
                for k, v in attrs:
                    if k.startswith("on") or (v and re.match(r"\s*javascript:", v, re.I)):
                        self.bad.append(f"<{tag} {k}>")
                if tag == "script" and not (re.fullmatch(r"(\.\./)*(site|pdk|charts)\.js", a.get("src") or "")
                                            or a.get("type") == "application/json"):
                    self.bad.append(f"<script {a}>")

        self.assertIn("script-src 'self';", page.CSP)
        self.assertNotRegex(page.CSP, r'["<>&]')                     # written into the attribute as it is
        self.assertNotIn("unsafe-eval", page.CSP)
        self.assertNotIn("'unsafe-inline'", page.CSP.split("script-src", 1)[1].split(";", 1)[0])
        pages = [p for p in self.site.files if p.endswith(".html")]
        self.assertGreater(len(pages), 100)
        for path in pages:
            h = self.site.files[path].decode("utf-8")
            with self.subTest(page=path):
                self.assertTrue('<meta charset="utf-8">\n<meta http-equiv="Content-Security-Policy" content="'
                                + page.CSP + '">\n' in h)
                self.assertEqual(h.count('http-equiv="Content-Security-Policy"'), 1)
                scan = Scan()
                scan.feed(h)
                self.assertEqual(scan.bad, [])

    def test_a_hand_drawn_figure_is_on_its_page(self):
        """The maintainers' inline SVG in the Booth record's writeup (decided 2026-11-16, the HTML writeups'
        demonstration): Figure 1, drawn by the site's rules for a writer's drawing, its caption the writer's (no
        generated line)."""
        rec = next(r for r in self.recs if r["record_hash"].startswith("15ca3004eb19"))
        h = self.page(rec)
        fig = h.split('<figure class="wfig" id="writeup-figure-1"><div class="wfig-box">', 1)[1].split("</figure>")[0]
        self.assertTrue(fig.startswith('<svg class="wfig-svg" viewBox="0 0 640 232" width="640.0" height="232.0" '
                                       'style="max-width:640.0px;min-width:426.7px" role="img" '
                                       'aria-labelledby="writeup-figure-1-t writeup-figure-1-d"'))
        self.assertIn("Drawn by the maintainers from the design.</figcaption>", fig)
        self.assertNotIn("generated from the design", fig)

    def test_the_rules_page_says_how_to_write_one(self):
        rules = self.site.files["rules.html"].decode("utf-8")
        self.assertIn('id="writeups"', rules)
        text = re.sub(r"<[^>]+>", " ", rules.split('id="writeups"', 1)[1].split("<h2", 1)[0])
        for phrase in ("leaderboard/writeups/TEMPLATE.html", "at most 60 characters", "never changes a record",
                       "the dead ends", "the proof strategy", "verify --offline", "inline SVG"):
            self.assertIn(phrase, " ".join(text.split()))


if __name__ == "__main__":
    unittest.main()
