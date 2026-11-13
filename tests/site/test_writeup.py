"""The writeups on the site (decided 2026-11-13, the owner's UI feedback items 3 and 6): site/writeup.py renders a
player's Markdown with everything escaped, no raw HTML, no image, links to http(s) addresses only, and headings whose
ids cannot take one of the page's; the record page shows the writeup as a card, its title as the page's heading, the
title in the submissions list and the charts' tooltips; a record without one shows a short prompt.

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

import md          # noqa: E402
import writeup     # noqa: E402


def render(body, title="T"):
    return writeup.render(f"# {title}\n\n{body}\n", source="w.md")[1]


def tags(h):
    """The tag names the HTML opens."""
    return sorted(set(re.findall(r"<([a-zA-Z][a-zA-Z0-9]*)", h)))


ALLOWED_TAGS = {"a", "code", "em", "h3", "h4", "h5", "h6", "li", "ol", "p", "pre", "span", "strong", "table", "tbody",
                "td", "th", "thead", "tr", "ul", "div", "hr"}


class RendererTest(unittest.TestCase):
    def test_raw_html_is_text(self):
        for body in ("<script>alert(1)</script>", "<img src=x onerror=alert(1)>", "<a href='javascript:x'>a</a>",
                     "<iframe src=https://evil.example></iframe>", "<style>body{display:none}</style>",
                     "<svg onload=alert(1)>", "<!-- comment --> <b>bold</b>", "&lt;script&gt; & <<x>>"):
            with self.subTest(body=body):
                h = render(body)
                self.assertNotIn("<script", h)
                self.assertNotIn("<img", h)
                self.assertNotIn("<iframe", h)
                self.assertNotIn("<style", h)
                self.assertNotIn("<svg", h)
                self.assertNotIn("<b>", h)
                self.assertNotRegex(h, r"<[^>]*\son[a-z]+=")   # no tag carries an event attribute (the text may)
                self.assertLessEqual(set(tags(h)), ALLOWED_TAGS)
                self.assertIn(html.escape(body.split(">")[0][:5], quote=False)[:4], h)

    def test_only_http_links_are_links(self):
        h = render("[a](https://example.org/x?y=1#z) [b](http://example.org)")
        self.assertIn('<a rel="nofollow ugc noopener" href="https://example.org/x?y=1#z">a</a>', h)
        self.assertIn('<a rel="nofollow ugc noopener" href="http://example.org">b</a>', h)
        for target in ("javascript:alert(1)", "JAVASCRIPT:alert(1)", "data:text/html,<script>x</script>",
                       "vbscript:x", "//evil.example/x", "/abs", "rel/path.html", "#frag", "file:///etc/passwd",
                       "https://ex\"onmouseover=alert(1)", "https://example.org/`x`", "https:///nohost",
                       "https://user@localhost/", "mailto:someone"):
            with self.subTest(target=target):
                h = render(f"[click]({target})")
                self.assertNotIn("<a ", h)
                self.assertNotIn('href="', h)

    def test_images_and_constructs_outside_the_subset_are_refused(self):
        for body in ("![x](https://example.org/x.png)", "![x](data:image/png;base64,AAAA)", "> quoted",
                     "[ref]: https://example.org", "Title\n=====", "see [^1]"):
            with self.subTest(body=body):
                with self.assertRaises(md.MarkdownError):
                    render(body)

    def test_code_is_escaped(self):
        h = render("```html\n</code></pre><script>alert(1)</script>\n```\n\n`</code><b>x</b>`")
        self.assertNotIn("<script", h)
        self.assertNotIn("<b>", h)
        self.assertIn("&lt;/code&gt;&lt;/pre&gt;&lt;script&gt;", h)

    def test_headings_start_under_the_card_and_never_take_a_page_id(self):
        h = render("# Sources\n\n## main\n\n### netlist")
        self.assertNotIn("<h1", h)
        self.assertNotIn("<h2", h)
        ids = re.findall(r'\bid="([^"]+)"', h)
        self.assertEqual(ids, ["writeup-sources", "writeup-main", "writeup-netlist"])
        self.assertIn('<h3 id="writeup-sources">', h)
        self.assertIn('<h4 id="writeup-netlist">', h)

    def test_the_title_is_plain_text(self):
        title, _ = writeup.render("# <b>Bold</b> & `code`\n\nbody\n", source="w.md")
        self.assertEqual(title, "<b>Bold</b> & `code`")          # the caller escapes it
        with self.assertRaises(ValueError):
            writeup.render("No title\n\nbody\n", source="w.md")
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
            path = os.path.join(self.lb.WRITEUPS_DIR, rec["record_hash"] + ".md")
            h = self.page(rec)
            with self.subTest(record=rec["record_hash"][:12]):
                card = re.search(r'<section class="card writeup[^"]*" id="writeup">(.*?)</section>', h, re.S)
                self.assertIsNotNone(card)
                main = h.split('id="main-col"', 1)[1].split('id="side-col"', 1)[0]
                self.assertLess(main.index('id="writeup"'), main.index('id="netlist"'))
                h1 = re.search(r"<h1\b[^>]*>(.*?)</h1>", h, re.S).group(1)
                if os.path.isfile(path):
                    with open(path, encoding="utf-8") as fh:
                        title = fh.readline()[2:].strip()
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

    def test_the_rules_page_says_how_to_write_one(self):
        rules = self.site.files["rules.html"].decode("utf-8")
        self.assertIn('id="writeups"', rules)
        text = re.sub(r"<[^>]+>", " ", rules.split('id="writeups"', 1)[1].split("<h2", 1)[0])
        for phrase in ("leaderboard/writeups/TEMPLATE.md", "at most 60 characters", "never changes a record",
                       "the dead ends", "the proof strategy"):
            self.assertIn(phrase, " ".join(text.split()))


if __name__ == "__main__":
    unittest.main()
