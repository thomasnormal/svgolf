"""A record's writeup on its page (decided 2026-11-13, the owner's UI feedback items 3 and 6).

A writeup is an optional Markdown file `leaderboard/writeups/<record_hash>.md`, kept OUTSIDE the record (no field
of the record and none of its hashes name it), so adding or improving one never changes a record. Its first line
`# <title>` is the submission's short title (plain text, at most TITLE_MAX characters), shown as the record page's
heading, in the task page's submissions list and in every chart tooltip; the rest is a blog-post-style account of
the design and its proof, shown on the record page. leaderboard.py `writeup_problems` checks a file's shape (its
name, UTF-8, the title line, the size cap, the characters); this module renders it.

The body is written by a player, so it is rendered SAFELY, by md.py (the site's own Markdown subset: headings,
paragraphs, lists, code spans and fenced code, emphasis, tables, links) under three rules of its own:

* nothing a writer types becomes markup: md.py has no raw HTML (every `<` is text, escaped), refuses images (no
  picture from another origin, no tracking pixel) and every construct outside its subset (a blockquote, a footnote,
  a reference link: MarkdownError, with the file and line);
* a link is a link only when its target is an absolute http or https address (`safe_target`); any other target
  (`javascript:`, `data:`, a relative path, an address with a quote or a control character) is shown as its text,
  linking nothing; a link carries rel="nofollow ugc noopener";
* the headings are the card's: `#` and `##` start at the card's sub-level (h3), and their anchors carry the prefix
  `writeup-`, so that no heading a writer picks can take an id of the page's own.

Standard library only, as md.py.
"""

import html
import re

import md

TITLE_MAX = 60                        # the title's length cap, in characters (leaderboard.py WRITEUP_TITLE_MAX)
ID_PREFIX = "writeup-"
_SAFE_URL = re.compile(r"https?://[A-Za-z0-9.-]+(?::[0-9]{1,5})?(?:[/?#][^\s\"'<>\\`\x00-\x1f\x7f]*)?")


def safe_target(target):
    """`target` when it is an absolute http or https address with a plain host name and no quote, angle bracket,
    backslash, backtick, space or control character; else None (the link's text is shown, linking nothing)."""
    return target if _SAFE_URL.fullmatch(target or "") else None


class _Slugger(md.Slugger):
    """md.py's heading anchors, each with the prefix `writeup-` (no heading takes an id of the page's own)."""

    def slug(self, text):
        return ID_PREFIX + super().slug(text)


def split(text):
    """(title, body, the body's first line number) of a writeup's text: the title is line 1 without its `# `; the
    body is everything after it. Raises ValueError when line 1 is not a title line (leaderboard.py checks this
    first, with its own words)."""
    first, _, body = text.partition("\n")
    m = re.fullmatch(r"# (\S(?:.*\S)?)", first)
    if not m:
        raise ValueError("line 1 is not `# <title>`")
    return m.group(1), body, 2


def render(text, *, source, highlight=None):
    """(title, the body as HTML) of a writeup's text (`source`: its path, for md.py's errors). The title is plain
    text (the caller escapes it); the body is md.py's rendering under the rules above. Raises md.MarkdownError for a
    construct outside the subset, ValueError for a text with no title line."""
    title, body, first = split(text)
    r = md.render(body, source=source, first_line=first, resolve_link=safe_target, highlight=highlight,
                  slugger=_Slugger(), heading_shift=1)
    out = r.html
    # md.py writes `<a href="...">` for a link it resolved, nothing else (a writer's `<` is escaped): mark each one
    out = out.replace('<a href="http', '<a rel="nofollow ugc noopener" href="http')
    # the headings start at h3 (the card's title is an h2): `#` would be h2 after the shift
    out = re.sub(r"<(/?)h2\b", r"<\1h3", out)
    return title, out


def fallback_title(design_name):
    """A record's title without a writeup: its design file's stem ("mul_tree.sv" -> "mul_tree")."""
    name = design_name.rsplit("/", 1)[-1]
    return name[:-3] if name.endswith(".sv") else name


def esc(s):
    return html.escape(str(s), quote=True)
