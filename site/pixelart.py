"""The pixel art of the site's look (style.css, "pixel golf course"): the home page's scene (a
pixel SV chip on the green beside the flag, the ball, trees and clouds, the night's moon and stars),
the small icons of its stats strip (a flag, a trophy, a ball), the logo of every page's header and
footer (the same chip, small) and the flag in the hole at the end of every page head's rule.

Every drawing is hand-drawn below as a map of characters, one character a pixel ('.' is empty),
and is written as inline SVG: one `<path>` per colour, its pixels merged into rectangles, drawn
with crisp edges. A colour is a class (`px-k`, `px-w`, ...), never a value: style.css gives each
class its fill from the theme's art tokens (`--px-*`), so the day and the night theme colour the
same drawing and the night's moon and stars are simply transparent by day. Decorative only: every
drawing is `aria-hidden` and carries no text. Deterministic: the same maps give the same bytes.
The favicon is the one drawing written with literal colours, as a file of its own (favicon.svg and
favicon-32.png): a browser tab has no style.css, so its colours are the day theme's tokens, written out.
"""

import struct
import zlib

# the colours: a map character -> the class of its pixels (style.css: `.px .px-<c> { fill: ... }`)
INKS = {
    "k": "k",    # outline ink
    "K": "k2",   # the chip face's frame
    "w": "w",    # white: the chip's face, the ball
    "c": "c",    # light shade of white: the face's lower edge, the ball's shadow side
    "C": "C",    # clouds
    "x": "x",    # cloud bellies
    "g": "g",    # the chip's body
    "h": "h",    # the chip's lit edge
    "G": "G",    # the chip's shaded edge
    "p": "p",    # gold: pins, legs, the pole's knob, the trophy
    "P": "P",    # gold in shade
    "o": "o",    # the flag pole
    "f": "f",    # the flag
    "F": "F",    # the flag in shade
    "q": "q",    # grass
    "l": "l",    # grass, lit (the hill's top edge)
    "v": "v",    # grass, dark (tufts)
    "T": "T",    # tree leaves
    "t": "t",    # tree leaves, lit
    "D": "D",    # tree leaves, shaded
    "b": "b",    # tree trunks
    "d": "d",    # the hole
    "m": "m",    # the moon (night only)
    "M": "M",    # the moon's craters (night only)
    "s": "s",    # stars (night only)
}

CHIP = [
    ".......kkk..kkk..kkk..kkk.......",
    ".......kpk..kpk..kpk..kpk.......",
    ".......kpk..kpk..kpk..kpk.......",
    "....kkkkkkkkkkkkkkkkkkkkkkkk....",
    "...kkhhhhhhhhhhhhhhhhhhhhhhkk...",
    "...khggggggggggggggggggggggGk...",
    "...khgKKKKKKKKKKKKKKKKKKKKgGk...",
    "kkkkhgKwwwwwwwwwwwwwwwwwwKgGkkkk",
    "kppkhgKwwwkkkkkwwkkwwkkwwKgGkppk",
    "kkkkhgKwwkkwwwwwwkkwwkkwwKgGkkkk",
    "...khgKwwkkwwwwwwkkwwkkwwKgGk...",
    "kkkkhgKwwwkkkkwwwkkwwkkwwKgGkkkk",
    "kppkhgKwwwwwwkkwwwkkkkwwwKgGkppk",
    "kkkkhgKwwwwwwkkwwwkkkkwwwKgGkkkk",
    "...khgKwwkkkkkwwwwwkkwwwwKgGk...",
    "kkkkhgKccccccccccccccccccKgGkkkk",
    "kppkhgKKKKKKKKKKKKKKKKKKKKgGkppk",
    "kkkkhggggggggggggggggggggggGkkkk",
    "...khggggggggggggggggggggggGk...",
    "...kkGGGGGGGGGGGGGGGGGGGGGGkk...",
    "....kkkkkkkkkkkkkkkkkkkkkkkk....",
    "........kpPk........kpPk........",
    "........kpPk........kpPk........",
    ".....kppppPk........kpPpppk.....",
    ".....kkkkkkk........kkkkkkk.....",
]

PENNANT = [
    "kk.............",
    "kfkk...........",
    "kfffkk.........",
    "kffffffkk......",
    "kfffffffffkk...",
    "kffffffffffffk.",
    "kfffffffffffFk.",
    "kfffffffFFFkk..",
    "kffffFFFkk.....",
    "kfFFFkk........",
    "kkkk...........",
]

BALL = [
    ".kkkk.",
    "kwwwwk",
    "kwwwck",
    "kwwcck",
    "kwccck",
    ".kkkk.",
]

HOLE = [
    "..ddddd..",
    "ddddddddd",
    "..ddddd..",
]

TREE = [
    "....TTT....",
    "..TTtttTT..",
    ".TTttttTTT.",
    ".TtttTTTTT.",
    "TTttTTTTTTD",
    "TTtTTTTTTTD",
    "TTTTTTTTTDD",
    ".TTTTTTTDD.",
    ".DTTTTTDDD.",
    "..DDDDDDD..",
    "....bbb....",
    ".....b.....",
    ".....b.....",
    ".....b.....",
]

TREE_SMALL = [
    "...TT...",
    ".TTttT..",
    "TTttTTT.",
    "TtTTTTTD",
    "TTTTTTDD",
    ".DTTTDD.",
    "..DDDD..",
    "...bb...",
    "...bb...",
    "...bb...",
]

CLOUD = [
    "........CCCCC.......",
    ".....CCCCCCCCCCC....",
    "..CCCCCCCCCCCCCCCCC.",
    "CCCCCCCCCCCCCCCCCCCC",
    ".xxxxxxxxxxxxxxxxxx.",
]

CLOUD_SMALL = [
    "....CCCC....",
    "..CCCCCCCCC.",
    "CCCCCCCCCCCC",
    ".xxxxxxxxxx.",
]

MOON = [
    "..mmmm..",
    ".mmmmmm.",
    "mmmmMmmm",
    "mmmmmmmm",
    "mmMmmmmm",
    "mmmmmmMm",
    ".mmmmmm.",
    "..mmmm..",
]

STAR = [
    ".s.",
    "sss",
    ".s.",
]

# the stats strip's icons, 12 x 12
ICON_FLAG = [
    ".k..........",
    ".kkk........",
    ".kffkk......",
    ".kffffkk....",
    ".kffffffkk..",
    ".kffffffFFk.",
    ".kfffFFFkk..",
    ".kfFFkk.....",
    ".kkk........",
    ".k..........",
    "lklll.......",
    "qqqqqqq.....",
]

ICON_TROPHY = [
    "..kkkkkkkk..",
    "kkkpppppPkkk",
    "kpkppppPPkpk",
    "kpkppppPPkpk",
    ".kkpppPPPkk.",
    "...kpPPPk...",
    "....kPPk....",
    ".....kk.....",
    "....kPPk....",
    "...kkkkkk...",
    "...kppPPk...",
    "..kkkkkkkk..",
]

ICON_BALL = [
    "....kkkk....",
    "..kkwwwwkk..",
    ".kwwwwwwwwk.",
    ".kwwcwwcwck.",
    "kwwwwwwwwwck",
    "kwcwwcwwcwck",
    "kwwwwwwwwcck",
    "kwwcwwcwccck",
    ".kwwwwwwcck.",
    ".kcwwccccck.",
    "..kkcccckk..",
    "....kkkk....",
]

# the logo, 17 x 14: the hero's chip, small, its face lettered S V (pixel letters 3 and 5 wide)
LOGO = [
    ".....p..p..p.....",
    ".kkkkkkkkkkkkkkk.",
    ".khhhhhhhhhhhhGk.",
    "pkhwwwwwwwwwwwGkp",
    ".khwwkkwkwwwkwGk.",
    "pkhwkwwwkwwwkwGkp",
    ".khwwkwwwkwkwwGk.",
    "pkhwwwkwwkwkwwGkp",
    ".khwkkwwwwkwwwGk.",
    "pkhcccccccccccGkp",
    ".kGGGGGGGGGGGGGk.",
    ".kkkkkkkkkkkkkkk.",
    "....kpk...kpk....",
    "....kkk...kkk....",
]

# the pennant of a page head's flag, 10 x 9
PENNANT_SMALL = [
    "kk........",
    "kfkk......",
    "kfffkk....",
    "kfffffkk..",
    "kffffffFk.",
    "kffffFFkk.",
    "kfffFkk...",
    "kfFkk.....",
    "kkk.......",
]

# the browser tab's mark, 16 x 16: the chip with a flag on its face (the logo's "SV" does not read at 16 px)
FAVICON = [
    "....p......p....",
    "....p......p....",
    "..kkkkkkkkkkkk..",
    "..kggggggggggk..",
    "..kgwwwwwwwwgk..",
    "ppkgwwkfffwwgkpp",
    "..kgwwkffwwwgk..",
    "..kgwwkfwwwwgk..",
    "..kgwwkwwwwwgk..",
    "..kgwwkwwwwwgk..",
    "ppkgqqkqqqqqgkpp",
    "..kgqqqqqqqqgk..",
    "..kggggggggggk..",
    "..kkkkkkkkkkkk..",
    "....p......p....",
    "....p......p....",
]

# its colours: the day theme's tokens (style.css :root), written out because the file stands alone. One set serves
# both themes: the dark outline carries the mark on a light tab strip, the white face and the gold pins on a dark one.
FAVICON_FILLS = {
    "k": "#24331c",   # --px-ink
    "g": "#9aa4ad",   # --px-chip-lo
    "w": "#ffffff",   # --px-face
    "p": "#f2b33d",   # --px-gold
    "f": "#ef5a2e",   # --px-flag
    "q": "#6cc04a",   # --px-grass
}


def _merge(cells):
    """The pixels of one colour as rectangles: runs along each row, then runs of equal runs down
    the rows. `cells` is a set of (x, y); the rectangles come out sorted, so the bytes are stable."""
    runs = {}
    for y in sorted({y for _, y in cells}):
        xs = sorted(x for x, yy in cells if yy == y)
        start = prev = None
        for x in xs + [None]:
            if x is not None and prev is not None and x == prev + 1:
                prev = x
                continue
            if start is not None:
                runs[(start, y)] = prev - start + 1
            start = prev = x
    rects = []
    taken = set()
    for (x, y) in sorted(runs, key=lambda k: (k[1], k[0])):
        if (x, y) in taken:
            continue
        w, h = runs[(x, y)], 1
        while runs.get((x, y + h)) == w:
            taken.add((x, y + h))
            h += 1
        rects.append((x, y, w, h))
    return rects


def _path_d(cells):
    """The `d` of one colour's `<path>`: its merged rectangles, each drawn from where the last one began (after `z`
    the pen is back at the rectangle's corner: move from there)."""
    d, at = "", None
    for x, y, w, h in _merge(cells):
        d += (f"M{x} {y}" if at is None else f"m{x - at[0]} {y - at[1]}") + f"h{w}v{h}h-{w}z"
        at = (x, y)
    return d


class Canvas:
    """A pixel canvas: sprites put on it in painter's order (a later pixel covers an earlier one)."""

    def __init__(self, w, h):
        self.w, self.h, self.px = w, h, {}

    def put(self, sprite, x, y):
        for j, row in enumerate(sprite):
            for i, ch in enumerate(row):
                if ch != "." and 0 <= x + i < self.w and 0 <= y + j < self.h:
                    self.px[(x + i, y + j)] = ch
        return self

    def rect(self, ch, x, y, w, h):
        return self.put([ch * w] * h, x, y)

    def svg(self, cls, scale=4, extra=""):
        """The canvas as inline SVG drawn `scale` CSS px to a pixel (style.css may resize it);
        `extra`: more attributes for the `<svg>`."""
        by = {}
        for (x, y), ch in self.px.items():
            by.setdefault(ch, set()).add((x, y))
        paths = []
        for ch in sorted(by, key=lambda c: list(INKS).index(c)):
            paths.append(f'<path class="px-{INKS[ch]}" d="{_path_d(by[ch])}"/>')
        return (f'<svg class="px {cls}" viewBox="0 0 {self.w} {self.h}" width="{self.w * scale}" '
                f'height="{self.h * scale}"{extra} shape-rendering="crispEdges" aria-hidden="true" focusable="false">'
                + "".join(paths) + "</svg>")


SCENE_W, SCENE_H = 120, 66


def _ground(x):
    """The top of the green at column x: a slope up from the left edge (where it meets the hero's
    ground, below the drawing) to the flag's plateau."""
    if x <= 92:
        return 40 + round(27 * ((92 - x) / 92) ** 2)
    return 40 + round(5 * ((x - 92) / 28) ** 2)


def scene():
    """The home page's hero art: the green with the chip, the flag and the ball, trees behind, clouds
    above (by night: dim clouds, the moon and stars). Its left fifth may lie under the hero's text
    (style.css), so the sky there stays empty."""
    c = Canvas(SCENE_W, SCENE_H)
    for x, y in ((30, 18), (44, 1), (54, 9), (84, 3), (116, 22), (116, 4), (84, 20), (105, 25)):
        c.put(STAR if (x + y) % 3 else ["s"], x, y)
    c.put(MOON, 28, 2)
    c.put(CLOUD, 36, 9).put(CLOUD_SMALL, 66, 2)
    for sprite, x in ((TREE_SMALL, 13), (TREE, 27), (TREE, 108)):
        base = max(_ground(i) for i in range(x, x + len(sprite[0])))
        c.put(sprite, x, base - len(sprite) + 2)
    for x in range(SCENE_W):
        top = _ground(x)
        c.rect("l", x, top, 1, 1).rect("q", x, top + 1, 1, SCENE_H - top - 1)
    for x in range(3, SCENE_W, 9):                         # tufts
        y = _ground(x) + 3 + (x * 7) % 5
        if y < SCENE_H - 1:
            c.put(["v.v", ".v."], x, y)
    pole = 98
    c.put(HOLE, pole - 4, _ground(pole) - 1)
    c.rect("k", pole - 1, 5, 4, _ground(pole) - 5).rect("o", pole, 5, 2, _ground(pole) - 5)
    c.put(["kkkk", "kppk", "kppk", "kkkk"], pole - 1, 2)
    c.put(PENNANT, pole + 2, 6)
    c.put(BALL, 84, _ground(86) - 5)
    chip_x = 46
    c.put(CHIP, chip_x, _ground(chip_x + 16) - len(CHIP) + 1)
    # anchored at the bottom right: where style.css narrows the drawing's box (a phone), the left of
    # the course (the far trees) is cut off and the chip and the flag stay
    return c.svg("scene", extra=' preserveAspectRatio="xMaxYMax slice"')


def icon(name):
    """A stats-strip icon: flag, trophy or ball."""
    sprite = {"flag": ICON_FLAG, "trophy": ICON_TROPHY, "ball": ICON_BALL}[name]
    return Canvas(12, 12).put(sprite, 0, 0).svg("ico")


def logo():
    """The site's mark beside its name in the header and the footer: the hero's chip, small."""
    return Canvas(len(LOGO[0]), len(LOGO)).put(LOGO, 0, 0).svg("logo", scale=2)


def hole_flag():
    """The flag in its hole that stands at the end of a page head's rule (the fairway)."""
    c = Canvas(16, 20)
    c.put(HOLE, 0, 17)
    c.rect("k", 3, 4, 4, 14).rect("o", 4, 4, 2, 14)
    c.put(["kkkk", "kppk", "kppk", "kkkk"], 3, 0)
    c.put(PENNANT_SMALL, 6, 4)
    return c.svg("hole-flag", scale=2)


def _favicon_cells():
    by = {}
    for y, row in enumerate(FAVICON):
        for x, ch in enumerate(row):
            if ch != ".":
                by.setdefault(ch, set()).add((x, y))
    return by


def favicon_svg():
    """favicon.svg: the tab's mark as a file, one `<path>` per colour with its fill written out (no style.css in a
    tab); no `<title>`: a tab icon carries no text."""
    by = _favicon_cells()
    paths = "".join(f'<path fill="{FAVICON_FILLS[ch]}" d="{_path_d(by[ch])}"/>' for ch in FAVICON_FILLS if ch in by)
    return ('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" width="16" height="16" '
            f'shape-rendering="crispEdges">{paths}</svg>\n').encode("utf-8")


def favicon_png(scale=2):
    """favicon-32.png: the mark as an RGBA PNG of 16 * `scale` pixels a side, transparent where the map is '.', for a
    browser that shows no SVG icon. Its IDAT is a STORED deflate stream (no compression), so the bytes do not depend on
    the zlib build: the same map gives the same file."""
    size = 16 * scale
    raw = bytearray()
    for y in range(size):
        raw.append(0)                                   # filter type 0 (none) for every row
        for x in range(size):
            ch = FAVICON[y // scale][x // scale]
            raw += (bytes.fromhex(FAVICON_FILLS[ch][1:]) + b"\xff") if ch != "." else b"\x00\x00\x00\x00"
    raw = bytes(raw)
    if len(raw) > 0xFFFF:
        raise ValueError("favicon_png: one stored block holds at most 65535 bytes")
    stream = (b"\x78\x01" + b"\x01" + struct.pack("<HH", len(raw), len(raw) ^ 0xFFFF) + raw
              + struct.pack(">I", zlib.adler32(raw) & 0xFFFFFFFF))

    def chunk(kind, data):
        return struct.pack(">I", len(data)) + kind + data + struct.pack(">I", zlib.crc32(kind + data) & 0xFFFFFFFF)

    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", size, size, 8, 6, 0, 0, 0))
            + chunk(b"IDAT", stream) + chunk(b"IEND", b""))
