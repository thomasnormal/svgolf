"""Static SVG charts for the svGolf site: standard library only, readable without JavaScript.

* `score_chart`: a task's combined score over time (a golf scorecard): a dot per entry by
  date, the best score so far as a step line, par as a dashed line, and the baselines as labelled
  levels in the right margin, each marked as not proved. Drawn on a linear and on a log axis
  (charts.js switches), each wide and compact (a phone's; style.css picks).
* `scatter_chart`: two metrics of a task's designs against each other, the Pareto front of the
  proved designs as a step line (the explorer's server-drawn view; charts.js redraws it for any
  pair of metrics with the same marks and classes).
* `bar_chart`: one horizontal bar per category (a record's gate mix).

Colours come from CSS classes (style.css: `.m-record`, `.m-reference`, `.m-baseline`, ...), so the
charts follow the page's light and dark themes. Marker SHAPES carry the identity too (filled,
ringed, hollow, crossed), never colour alone, and every chart on the site sits next to a table
with the same numbers. Each mark is a `<g class="mark">` with a `<title>` (the browser's tooltip),
a `data-tip` (charts.js's tooltip: one line per row) and data attributes for tests and scripts;
a mark with somewhere to go is wrapped in a link.

Output is deterministic: coordinates are rounded to 0.1 and nothing depends on dict or set order.
"""

import datetime
import html
import math

W, H = 640, 400                       # the viewBox of the scatter
MARGIN = {"left": 72, "right": 20, "top": 16, "bottom": 52}
MONTHS = ("Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec")
KIND_ORDER = {"baseline": 0, "reference": 1, "record": 2}   # records drawn on top


def _f(v):
    """A coordinate, rounded to 0.1 (a fixed text form keeps the output stable)."""
    s = f"{round(v, 1):.1f}"
    return "0.0" if s == "-0.0" else s


def _esc(s):
    return html.escape(str(s), quote=True)


def _nice_step(span, target):
    raw = span / max(1, target)
    mag = 10 ** math.floor(math.log10(raw)) if raw > 0 else 1
    for m in (1, 2, 2.5, 5, 10):
        if raw <= m * mag:
            return m * mag
    return 10 * mag


class Scale:
    """A linear or logarithmic map from data values to pixels, with ticks. A range spanning more
    than 10x (positive values only) is drawn on a log axis; `log` forces the choice either way
    (a log axis needs positive values)."""

    def __init__(self, lo, hi, px0, px1, *, log=None, integer=False):
        if lo > hi:
            lo, hi = hi, lo
        self.log = (lo > 0 and hi / lo > 10) if log is None else (log and lo > 0)
        self.integer = integer
        nonnegative = lo >= 0
        if self.log:
            lo, hi = (lo / 1.25, hi * 1.25) if hi / lo > 1.5 else (lo / 1.12, hi * 1.12)
        elif hi == lo:
            pad = 1 if integer else (abs(lo) * 0.1 or 1)
            lo, hi = lo - pad, hi + pad
        else:
            pad = (hi - lo) * 0.08
            lo, hi = lo - pad, hi + pad
        if integer and not self.log:
            lo, hi = math.floor(lo), math.ceil(hi)
        if nonnegative and not self.log:
            lo = max(0, lo)
        self.lo, self.hi, self.px0, self.px1 = lo, hi, px0, px1

    def __call__(self, v):
        if self.log:
            a, b, v = math.log10(self.lo), math.log10(self.hi), math.log10(v)
        else:
            a, b = self.lo, self.hi
        return self.px0 + (v - a) / (b - a) * (self.px1 - self.px0)

    def ticks(self, target=6):
        if self.log:
            e0, e1 = math.floor(math.log10(self.lo)), math.ceil(math.log10(self.hi))
            for mults in ((1,), (1, 2, 5), (1, 2, 3, 4, 5, 6, 7, 8, 9)):
                out = [m * 10 ** e for e in range(e0, e1 + 1) for m in mults if self.lo <= m * 10 ** e <= self.hi]
                if len(out) >= 3:       # thinned to about target + 2 (8 on a wide drawing, 6 on a phone's)
                    return out[:: max(1, math.ceil(len(out) / max(4, target + 2)))]
            # less than one step of 1..9 inside: linear ticks are positions on a log axis too
        step = _nice_step(self.hi - self.lo, target)
        if self.integer:
            step = max(1, round(step))
        v = math.ceil(self.lo / step) * step
        out = []
        while v <= self.hi + 1e-9:
            if not self.log or v > 0:
                out.append(round(v, 6))
            v += step
        return out


def num(v):
    """A tick label: 1200 -> '1200', 2.5 -> '2.5', 20000 -> '20k', 1500000 -> '1.5M'."""
    a = abs(v)
    if a >= 1e6:
        return f"{v / 1e6:.3g}M"
    if a >= 1e4:
        return f"{v / 1e3:.3g}k"
    return f"{v:.4g}"


def tick(v):
    """An axis tick label: `num`'s form, with as many more digits as it takes to say the tick's value
    exactly (ticks 2.5k apart read 147.5k, 150k, 152.5k, never 148k, 150k, 153k)."""
    a = abs(v)
    scale, unit = (1e6, "M") if a >= 1e6 else (1e3, "k") if a >= 1e4 else (1, "")
    for digits in range(3 if unit else 4, 10):
        s = f"{v / scale:.{digits}g}"
        if abs(float(s) * scale - v) <= 1e-9 * max(1.0, a):
            return s + unit
    return f"{v / scale:.10g}{unit}"


def tick_rows(xs, labels, char_w, gap=6):
    """The row (0 or 1) of each x-axis tick label, in tick order: a label that would overlap the one
    before it (`char_w`: the width of a character, in viewBox units) drops to a second row, so close
    named ticks ('bfloat16' and 'binary16' on a phone) stay readable."""
    rows, ends = [], [-math.inf, -math.inf]
    for x, label in zip(xs, labels):
        half = len(label) * char_w / 2
        row = 0 if x - half >= ends[0] + gap else 1 if x - half >= ends[1] + gap else 0
        rows.append(row)
        ends[row] = x + half
    return rows


class Frame:
    """The drawing area of a chart: the viewBox (w x h) and the plot inside its margins."""

    def __init__(self, w=W, h=H, left=MARGIN["left"], right=MARGIN["right"], top=MARGIN["top"],
                 bottom=MARGIN["bottom"]):
        self.w, self.h = w, h
        self.left, self.right, self.top, self.bottom = left, w - right, top, h - bottom


def _axes(fr, xs, ys, x_label, y_label, x_fmt=tick, y_fmt=tick, x_ticks=None, target=6, compact=False,
          x_grid=True, x_rows=None):
    """Gridlines, tick labels and axis titles. `compact` (a phone's drawing, its text set larger):
    the y title runs across the top-left corner instead of up the side, where it would collide
    with the tick labels. `x_grid`: vertical gridlines (the score chart's dates need none).
    `x_rows`: each x tick label's row (`tick_rows`; the second row 16 units lower)."""
    parts = ['<g class="axes">']
    for v in ys.ticks(target):
        y = ys(v)
        parts.append(f'<line class="grid" x1="{_f(fr.left)}" x2="{_f(fr.right)}" y1="{_f(y)}" y2="{_f(y)}"/>')
        parts.append(f'<text class="tick" x="{_f(fr.left - 8)}" y="{_f(y + 4)}" text-anchor="end">'
                     f"{_esc(y_fmt(v))}</text>")
    for k, v in enumerate(x_ticks if x_ticks is not None else xs.ticks(target)):
        x = xs(v)
        if x_grid:
            parts.append(f'<line class="grid" x1="{_f(x)}" x2="{_f(x)}" y1="{_f(fr.top)}" y2="{_f(fr.bottom)}"/>')
        row = x_rows[k] if x_rows else 0
        parts.append(f'<text class="tick" x="{_f(x)}" y="{_f(fr.bottom + 18 + 16 * row)}" text-anchor="middle">'
                     f"{_esc(x_fmt(v))}</text>")
    parts.append(f'<line class="axis" x1="{_f(fr.left)}" x2="{_f(fr.right)}" y1="{_f(fr.bottom)}" y2="{_f(fr.bottom)}"/>')
    parts.append(f'<line class="axis" x1="{_f(fr.left)}" x2="{_f(fr.left)}" y1="{_f(fr.top)}" y2="{_f(fr.bottom)}"/>')
    parts.append(f'<text class="axis-title" x="{_f((fr.left + fr.right) / 2)}" y="{_f(fr.h - 8)}" '
                 f'text-anchor="middle">{_esc(x_label)}</text>')
    if compact:
        parts.append(f'<text class="axis-title" x="{_f(4)}" y="{_f(fr.top - 12)}" text-anchor="start">'
                     f"{_esc(y_label)}</text>")
    else:
        parts.append(f'<text class="axis-title" transform="translate(14 {_f((fr.top + fr.bottom) / 2)}) rotate(-90)" '
                     f'text-anchor="middle">{_esc(y_label)}</text>')
    parts.append("</g>")
    return parts


def _svg(fr, parts, title, desc, cls="chart"):
    return (f'<svg class="{cls}" viewBox="0 0 {fr.w} {fr.h}" role="img" aria-label="{_esc(title)}" '
            f'xmlns="http://www.w3.org/2000/svg"><title>{_esc(title)}</title>'
            f"<desc>{_esc(desc)}</desc>" + "".join(parts) + "</svg>")


def marker(kind, x, y, banned=False, r=5):
    """The marker shape of one kind of point, centred at (x, y)."""
    X, Y = _f(x), _f(y)
    if kind == "record":
        return f'<circle class="m-record" cx="{X}" cy="{Y}" r="{r * 1.3:g}"/>'
    if kind == "reference":
        return (f'<circle class="m-reference-ring" cx="{X}" cy="{Y}" r="{r * 1.5:g}"/>'
                f'<circle class="m-reference" cx="{X}" cy="{Y}" r="{r * 0.7:g}"/>')
    if banned:
        return (f'<circle class="m-baseline" cx="{X}" cy="{Y}" r="{r}"/>'
                f'<path class="m-banned" d="M{_f(x - 6)} {_f(y - 6)}L{_f(x + 6)} {_f(y + 6)}'
                f'M{_f(x - 6)} {_f(y + 6)}L{_f(x + 6)} {_f(y - 6)}"/>')
    return f'<circle class="m-baseline" cx="{X}" cy="{Y}" r="{r}"/>'


def legend_icon(kind, banned=False):
    """A small standalone SVG of a marker, for HTML legends."""
    return (f'<svg class="legend-icon" viewBox="0 0 20 20" width="20" height="20" aria-hidden="true">'
            f"{marker(kind, 10, 10, banned)}</svg>")


def line_icon(cls):
    """A small standalone SVG of a line style (`frontier`, `par-line`, `level`), for HTML legends."""
    pts = "2,6 10,6 10,14 18,14" if cls == "frontier" else "2,10 18,10"
    return (f'<svg class="legend-icon" viewBox="0 0 20 20" width="20" height="20" aria-hidden="true">'
            f'<polyline class="{cls}" points="{pts}"/></svg>')


def step_points(front):
    """The staircase through a minimization frontier: (x, y) points sorted by x, joined by
    horizontal-then-vertical segments."""
    pts = sorted(set(front))
    out = []
    for k, (d, a) in enumerate(pts):
        if k:
            out.append((d, pts[k - 1][1]))
        out.append((d, a))
    return out


def _mark(p, x, y, r=5):
    """One mark: a `<g>` (with its tooltip and data attributes) around the marker, in a link when
    the point has an `href`. `p["attrs"]` are extra data attributes (name -> value)."""
    attrs = "".join(f' data-{k}="{_esc(v)}"' for k, v in sorted((p.get("attrs") or {}).items()))
    tip = p.get("tip") or [p.get("label", "")]
    cls = "mark" + (f" {p['cls']}" if p.get("cls") else "")
    g = (f'<g class="{cls}" data-kind="{_esc(p["kind"])}"{attrs} data-tip="{_esc(chr(10).join(tip))}">'
         f"<title>{_esc(' · '.join(tip))}</title>"
         f'<circle class="hit" cx="{_f(x)}" cy="{_f(y)}" r="12"/>{marker(p["kind"], x, y, p.get("banned", False), r)}</g>')
    if p.get("href"):
        return f'<a href="{_esc(p["href"])}" aria-label="{_esc(p.get("label") or tip[0])}">{g}</a>'
    return g


# ---------------------------------------------------------------------------
# the score chart
# ---------------------------------------------------------------------------

# the frames: a wide drawing for a desktop column (about 1:1 there), a compact one for a phone (its
# text set larger by style.css); a compact score chart names the baselines under it, not beside it
SCORE_FRAME = dict(w=960, h=330, left=66, right=196, top=18, bottom=44)
SCORE_COMPACT = dict(w=420, h=330, left=56, right=16, top=32, bottom=46)      # top: room for the y title
SCATTER_FRAME = dict(w=960, h=430, left=82, right=24, top=18, bottom=56)
SCATTER_COMPACT = dict(w=420, h=400, left=60, right=16, top=32, bottom=52)


def _ordinal(date):
    return datetime.date.fromisoformat(date[:10]).toordinal()


def date_label(ordinal, same_year=True):
    d = datetime.date.fromordinal(int(ordinal))
    return f"{d.day} {MONTHS[d.month - 1]}" if same_year else f"{MONTHS[d.month - 1]} {d.year}"


def _spread(ys, lo, hi, gap):
    """Label positions near `ys` (sorted ascending), at least `gap` apart, kept within [lo, hi]."""
    out = []
    for y in ys:
        out.append(max(y, out[-1] + gap) if out else max(y, lo))
    over = out[-1] - hi if out else 0
    if over > 0:                                   # pushed past the bottom: shift the run back up
        out = [y - over for y in out]
        for k in range(len(out) - 2, -1, -1):
            out[k] = min(out[k], out[k + 1] - gap)
    return out


def score_chart(entries, *, par=None, levels=(), log=False, title, unit, value_fmt=num, until=None,
                compact=False):
    """The combined score over time. `entries`: dicts with id, kind (record | reference), date
    (YYYY-MM-DD), value (the score), score (its exact integer, for the order of equal values),
    tip (lines), href, attrs, banned. `par`: {"value", "label"} or None. `levels`: the baselines,
    dicts with id, name, value, banned, tip. `until`: the date the chart is as of (YYYY-MM-DD).
    The step line is the best score so far, from the first entry to the right edge; a dot that set
    a new best is drawn larger. `compact`: the phone drawing (SCORE_COMPACT), whose baselines are
    unlabelled levels (the page names them under the chart). Returns "" with no entry."""
    dated = [e for e in entries if e.get("date")]
    if not dated:
        return ""
    fr = Frame(**(SCORE_COMPACT if compact else SCORE_FRAME))
    target = 4 if compact else 6
    days = [_ordinal(e["date"]) for e in dated]
    d0, d1 = min(days), max(days)
    # the axis ends at `until` (the date the page is as of) or a day after the last entry, and covers
    # at least two weeks; the best-so-far line runs on to its end
    d1 = max(d1 + 1, _ordinal(until) if until else d1 + 1)
    d0 = min(d0 - 1, d1 - 14)
    xs = Scale(d0, d1, fr.left + 10, fr.right - 10, log=False, integer=True)
    values = [e["value"] for e in dated] + [lv["value"] for lv in levels] + ([par["value"]] if par else [])
    ys = Scale(min(values), max(values), fr.bottom, fr.top, log=log)
    same_year = datetime.date.fromordinal(xs.lo).year == datetime.date.fromordinal(xs.hi).year
    step = max(1, round(_nice_step(xs.hi - xs.lo, target)))
    step = next((s for s in (1, 2, 7, 14, 28, 56, 91, 182, 365) if s >= step), step)
    first = xs.lo + (-xs.lo) % step if step < 7 else xs.lo + (7 - datetime.date.fromordinal(xs.lo).weekday()) % 7
    x_ticks = [v for v in range(first, xs.hi + 1, step)]
    parts = _axes(fr, xs, ys, "date entered", f"score ({unit})" + (", log scale" if ys.log else ""),
                  x_fmt=lambda v: date_label(v, same_year), x_ticks=x_ticks, target=target, compact=compact,
                  x_grid=False)
    # the levels: unproved baselines, a dotted line across and a label in the right margin; the
    # line (a wide invisible stroke over it, so that it is easy to point at) and the label carry
    # the baseline's tooltip
    labels = []
    for lv in sorted(levels, key=lambda lv: (-lv["value"], lv["id"])):
        y = ys(lv["value"])
        parts.append(f'<g class="level-mark" data-kind="baseline" data-id="{_esc(lv["id"])}" '
                     f'data-tip="{_esc(chr(10).join(lv["tip"]))}">'
                     f'<title>{_esc(" · ".join(lv["tip"]))}</title>'
                     f'<line class="level" x1="{_f(fr.left)}" x2="{_f(fr.right)}" y1="{_f(y)}" y2="{_f(y)}"/>'
                     f'<line class="level-hit" x1="{_f(fr.left)}" x2="{_f(fr.right)}" y1="{_f(y)}" y2="{_f(y)}"/></g>')
        labels.append((y, "level", lv))
        if compact:
            parts.append(marker("baseline", fr.right - 5, y, lv.get("banned"), 3))
    if par:
        y = ys(par["value"])
        parts.append(f'<line class="par-line" x1="{_f(fr.left)}" x2="{_f(fr.right)}" y1="{_f(y)}" y2="{_f(y)}">'
                     f'<title>{_esc(par["label"])}</title></line>')
        labels.append((y, "par", par))
        if compact:
            parts.append(f'<text class="lv-name lv-par" x="{_f(fr.left + 6)}" y="{_f(y - 6)}">PAR</text>')
    if compact:
        labels = []
    # the margin labels: par and the levels, pushed apart so that none overlap
    labels.sort(key=lambda t: (t[0], t[1]))
    spots = _spread([y for y, _, _ in labels], fr.top + 8, fr.bottom - 10, 27)
    lx = fr.right + 10
    for (y, what, item), ly in zip(labels, spots):
        parts.append(f'<path class="leader" d="M{_f(fr.right)} {_f(y)}L{_f(lx - 4)} {_f(ly)}"/>')
        if what == "par":
            parts.append(f'<text class="lv-name lv-par" x="{_f(lx)}" y="{_f(ly + 1)}">PAR</text>'
                         f'<text class="lv-note" x="{_f(lx)}" y="{_f(ly + 12)}">{_esc(value_fmt(item["value"]))}'
                         " · proved</text>")
        else:
            parts.append(f'<g class="lv-label" data-tip="{_esc(chr(10).join(item["tip"]))}">'
                         f'{marker("baseline", lx + 3, ly - 3, item.get("banned"), 3)}'
                         f'<text class="lv-name" x="{_f(lx + 11)}" y="{_f(ly + 1)}">{_esc(item["name"])}</text>'
                         f'<text class="lv-note" x="{_f(lx + 11)}" y="{_f(ly + 12)}">{_esc(value_fmt(item["value"]))}'
                         f' · {"banned op" if item.get("banned") else "not proved"}</text></g>')
    # the best score so far
    order = sorted(dated, key=lambda e: (e["date"], e["score"], e["id"]))
    best, stair, setters = None, [], set()
    for e in order:
        if best is None or e["score"] < best["score"]:
            x = _ordinal(e["date"])
            if best is not None:
                stair.append((x, best["value"]))
            best = e
            stair.append((x, e["value"]))
            setters.add(e["id"])
    coords = " ".join(f"{_f(xs(d))},{_f(ys(v))}" for d, v in stair) + f" {_f(fr.right)},{_f(ys(stair[-1][1]))}"
    # a faint drop line from each dot to its date
    for e in sorted(dated, key=lambda e: (e["date"], e["id"])):
        x, y = xs(_ordinal(e["date"])), ys(e["value"])
        parts.append(f'<line class="drop" x1="{_f(x)}" x2="{_f(x)}" y1="{_f(y)}" y2="{_f(fr.bottom)}"/>')
    parts.append(f'<polyline class="frontier" points="{coords}"><title>the best score so far</title></polyline>')
    for e in sorted(dated, key=lambda e: (KIND_ORDER[e["kind"]], e["id"] in setters, e["date"], e["id"])):
        p = dict(e, cls="best" if e["id"] in setters else "")
        parts.append(_mark(p, xs(_ordinal(e["date"])), ys(e["value"]), r=5.5 if e["id"] in setters else 4))
    desc = (f"{len(dated)} entries by date (x) and score in {unit} (y); the line is the best score so far"
            + (", the dashed line par" if par else "")
            + (f", and {len(levels)} unproved baselines are labelled on the right" if levels else "")
            + ". The table under the chart lists the same numbers.")
    return _svg(fr, parts, title, desc, cls="chart compact" if compact else "chart")


# ---------------------------------------------------------------------------
# the explorer's scatter
# ---------------------------------------------------------------------------

def shared_tips(points, on=()):
    """Designs drawn at the same (x, y) hide one another, so each of them gets one tooltip naming
    them all: "n designs at this point", a line per design (its `brief`, else its name; the ones on
    the front first, then submissions, references, baselines) and the values (`axis_tip`, the first
    one's). A point alone keeps its own tip. Returns new dicts; the order of `points` is kept."""
    groups = {}
    for p in points:
        groups.setdefault((p["x"], p["y"]), []).append(p)
    out = []
    for p in points:
        g = groups[(p["x"], p["y"])]
        if len(g) < 2:
            out.append(p)
            continue
        g = sorted(g, key=lambda q: (q["id"] not in on, -KIND_ORDER[q["kind"]], q["id"]))
        tip = ([f"{len(g)} designs at this point"] + [q.get("brief") or (q.get("tip") or [q["id"]])[0] for q in g]
               + list(g[0].get("axis_tip") or []))
        out.append(dict(p, tip=tip, label=(p.get("tip") or [p["id"]])[0]))     # the link keeps its own name
    return out


def scatter_chart(points, *, x_label, y_label, x_log=None, y_log=None, x_integer=False, y_integer=False,
                  front=(), title, front_label="the Pareto front of the proved designs", compact=False):
    """Two metrics against each other. `points`: dicts with id, kind, x, y, banned, tip, href,
    attrs. `front`: the ids on the Pareto front (drawn full strength, joined by a step line; every
    other mark is muted). Lower is better on both axes. `compact`: the phone drawing."""
    if not points:
        return ""
    fr = Frame(**(SCATTER_COMPACT if compact else SCATTER_FRAME))
    target = 4 if compact else 6
    xs = Scale(min(p["x"] for p in points), max(p["x"] for p in points), fr.left, fr.right, log=x_log,
               integer=x_integer)
    ys = Scale(min(p["y"] for p in points), max(p["y"] for p in points), fr.bottom, fr.top, log=y_log,
               integer=y_integer)
    parts = _axes(fr, xs, ys, x_label + (", log scale" if xs.log else ""), y_label + (", log scale" if ys.log else ""),
                  target=target, compact=compact)
    on = set(front)
    points = shared_tips(points, on)
    fpts = [(p["x"], p["y"]) for p in points if p["id"] in on]
    if fpts:
        # the staircase from the top edge down through the front and on to the right edge: what is
        # above and to the right of it is beaten
        stair = step_points(fpts)
        coords = (f"{_f(xs(stair[0][0]))},{_f(fr.top)} " + " ".join(f"{_f(xs(x))},{_f(ys(y))}" for x, y in stair)
                  + f" {_f(fr.right)},{_f(ys(stair[-1][1]))}")
        parts.append(f'<polyline class="frontier" points="{coords}"><title>{_esc(front_label)}</title></polyline>')
    for p in sorted(points, key=lambda p: (p["id"] in on, KIND_ORDER[p["kind"]], p["y"], p["x"], p["id"])):
        parts.append(_mark(dict(p, cls="on-front" if p["id"] in on else "off-front"), xs(p["x"]), ys(p["y"])))
    desc = (f"{len(points)} designs by {x_label} (x) and {y_label} (y); lower is better on both. "
            "The table under the chart lists the same numbers.")
    return _svg(fr, parts, title, desc, cls="chart compact" if compact else "chart")


# ---------------------------------------------------------------------------
# a record page's area-time plot
# ---------------------------------------------------------------------------

AREA_TIME_FRAME = dict(w=960, h=430, left=82, right=24, top=18, bottom=56)
AREA_TIME_COMPACT = dict(w=420, h=400, left=60, right=16, top=32, bottom=52)


def _clamp(v, lo, hi):
    return max(lo, min(hi, v))


def area_time_chart(points, *, subject, view, x_label, y_label, title, front=(), par=None, compact=False):
    """One design among its task's designs: area (x) against the ranked time (y), lower left better. `points`:
    dicts with id, kind, x, y, banned, tip, href, label, attrs. `subject`: the id of the page's design, drawn with a
    halo and labelled; `par`: {"id", "score" (x * y), "label"} or None: par is labelled and its score curve (x * y =
    par's) drawn, under which a design beats par on the ranked score; `front`: the ids on the Pareto front of the
    entries (the step line). `view`: (x0, x1, y0, y1) in data units, what the plot shows: a design outside it is not
    drawn but counted at the edge it lies past (one past a corner on both edges), except the subject and par, which
    are drawn clamped to the edge, faded. A view spanning more than 10x on an axis is drawn on a log axis there.
    Returns "" without points."""
    if not points:
        return ""
    fr = Frame(**(AREA_TIME_COMPACT if compact else AREA_TIME_FRAME))
    target = 4 if compact else 6
    x0, x1, y0, y1 = view
    xs = Scale(x0, x1, fr.left, fr.right, log=x0 > 0 and x1 / x0 > 10)
    ys = Scale(y0, y1, fr.bottom, fr.top, log=y0 > 0 and y1 / y0 > 10)
    xs.lo, xs.hi, ys.lo, ys.hi = x0, x1, y0, y1                # the view itself (fitted and padded by the caller)
    parts = _axes(fr, xs, ys, x_label + (", log scale" if xs.log else ""), y_label + (", log scale" if ys.log else ""),
                  target=target, compact=compact)
    inside = lambda p: x0 <= p["x"] <= x1 and y0 <= p["y"] <= y1        # noqa: E731
    if par and par.get("score"):
        # par's score curve, x * y = c, sampled evenly across the plot's width and kept inside it
        pts, n = [], 48
        for k in range(n + 1):
            px = fr.left + (fr.right - fr.left) * k / n
            xv = (10 ** (math.log10(x0) + (math.log10(x1) - math.log10(x0)) * k / n)) if xs.log else x0 + (x1 - x0) * k / n
            if xv <= 0:
                continue
            yv = par["score"] / xv
            if y0 <= yv <= y1:
                pts.append(f"{_f(px)},{_f(ys(yv))}")
        if len(pts) >= 2:
            parts.append(f'<polyline class="iso" points="{" ".join(pts)}"><title>{_esc(par["label"])}</title></polyline>')
    on = set(front)
    fpts = [(p["x"], p["y"]) for p in points if p["id"] in on]
    if fpts:
        stair = step_points(fpts)
        cx = lambda v: _clamp(xs(v), fr.left, fr.right)     # noqa: E731
        cy = lambda v: _clamp(ys(v), fr.top, fr.bottom)     # noqa: E731
        coords = (f"{_f(cx(stair[0][0]))},{_f(fr.top)} " + " ".join(f"{_f(cx(x))},{_f(cy(y))}" for x, y in stair)
                  + f" {_f(fr.right)},{_f(cy(stair[-1][1]))}")
        parts.append(f'<polyline class="frontier" points="{coords}"><title>the Pareto front of the entries'
                     "</title></polyline>")
    keep = {subject} | ({par["id"]} if par else set())
    edges = {"left": 0, "right": 0, "above": 0, "below": 0}
    drawn = []
    for p in points:
        if inside(p):
            drawn.append((p, False))
            continue
        if p["x"] < x0:
            edges["left"] += 1
        elif p["x"] > x1:
            edges["right"] += 1
        if p["y"] < y0:
            edges["below"] += 1
        elif p["y"] > y1:
            edges["above"] += 1
        if p["id"] in keep:
            drawn.append((p, True))
    pts = shared_tips([p for p, _ in drawn], on)
    clamped = {p["id"] for p, c in drawn if c}
    order = sorted(pts, key=lambda p: (p["id"] == subject, p["id"] in on, KIND_ORDER[p["kind"]], p["y"], p["x"], p["id"]))
    for p in order:
        x, y = _clamp(xs(p["x"]), fr.left, fr.right), _clamp(ys(p["y"]), fr.top, fr.bottom)
        cls = ("subject " if p["id"] == subject else "") + ("on-front" if p["id"] in on else "off-front") \
            + (" clamped" if p["id"] in clamped else "")
        if p["id"] == subject:
            parts.append(f'<circle class="halo" cx="{_f(x)}" cy="{_f(y)}" r="13"/>')
        parts.append(_mark(dict(p, cls=cls), x, y))
    # the labels: this design, and par (when it is another design)
    me = next((p for p in order if p["id"] == subject), None)
    for p in order:
        if p["id"] != subject and not (par and p["id"] == par["id"]):
            continue
        at_me = me is not None and p is not me and (p["x"], p["y"]) == (me["x"], me["y"])
        if at_me:
            continue                                   # par at this design's point: one label says both
        x, y = _clamp(xs(p["x"]), fr.left, fr.right), _clamp(ys(p["y"]), fr.top, fr.bottom)
        if p["id"] == subject:
            twin = par and par["id"] != subject and any(q["id"] == par["id"] and (q["x"], q["y"]) == (p["x"], p["y"])
                                                        for q in order)
            text = "this design" + (" · par" if par and par["id"] == subject else " · par's numbers" if twin else "")
        else:
            text = "par"
        if p["id"] in clamped:
            text += " (beyond view)"
        # this design's label above its mark, par's below (the two are often close); flipped at the plot's edge
        right = x < (fr.left + fr.right) / 2
        up = p["id"] == subject
        ly = y - 17 if up else y + 25
        if ly < fr.top + 10 or ly > fr.bottom - 4:
            ly = y + 25 if up else y - 17
        parts.append(f'<text class="dlabel" x="{_f(x + 6 if right else x - 6)}" y="{_f(ly)}" '
                     f'text-anchor="{"start" if right else "end"}">{_esc(text)}</text>')
    # the counters: designs past each edge
    ctr = {"left": ("◂ {n}", fr.left + 6, (fr.top + fr.bottom) / 2, "start"),
           "right": ("{n} ▸", fr.right - 6, (fr.top + fr.bottom) / 2, "end"),
           "above": ("▴ {n}", (fr.left + fr.right) / 2, fr.top + 14, "middle"),
           "below": ("▾ {n}", (fr.left + fr.right) / 2, fr.bottom - 8, "middle")}
    for edge in ("left", "right", "above", "below"):
        n = edges[edge]
        if n:
            fmt, x, y, anchor = ctr[edge]
            parts.append(f'<text class="ctr" x="{_f(x)}" y="{_f(y)}" text-anchor="{anchor}" data-edge="{edge}">'
                         f'<title>{n} design{"" if n == 1 else "s"} beyond the view ({edge})</title>{_esc(fmt.format(n=n))}'
                         "</text>")
    beyond = sum(1 for p in points if not inside(p))
    desc = (f"{len(points)} designs by {x_label} (x) and {y_label} (y), this one ringed; lower left is better"
            + (f"; {beyond} beyond the view, counted at its edges" if beyond else "")
            + ". The table under the chart lists the same numbers.")
    return _svg(fr, parts, title, desc, cls="chart pa compact" if compact else "chart pa")


# ---------------------------------------------------------------------------
# the scaling view: one metric against the task's parameter, a line per design
# ---------------------------------------------------------------------------

LINES_FRAME = dict(w=960, h=430, left=82, right=196, top=18, bottom=56)
LINES_COMPACT = dict(w=420, h=400, left=60, right=116, top=32, bottom=52)
LABEL_CHARS = {False: 26, True: 13}          # a margin name's length, wide and compact (set at 13px on a phone)
TICK_CHAR_W = {False: 6.6, True: 9.0}        # a tick label character's width: 0.6 em of 11px (wide), 15px (phone)


def short(name, n):
    """`name` cut to `n` characters with an ellipsis (the full name is in the tooltip and the table)."""
    return name if len(name) <= n else name[:n - 1] + "…"


def line_chart(lines, *, x_label, y_label, x_ticks, x_fmt=tick, x_log=None, y_log=None, y_integer=False, title,
               guide=None, compact=False):
    """One metric of a task's designs against its parameter. `lines`: dicts with id, kind (record | reference |
    baseline), banned, name (the label), tip (the line's tooltip lines), href and pts, each {x, y, tip} (sorted by
    x; a line needs two points). Each line is a polyline (a baseline's dashed: not proved) with a mark per point and
    its name in the right margin at its last point (the names pushed apart so that none overlap, a leader to each);
    the line, its marks and its name are one group, so pointing at any of them picks the line out. `x_ticks`: the
    parameter values (the axis is labelled at exactly those; labels too close for one row take two, and the
    drawing grows by the second row). `guide`: {"y", "label"}, a dashed level (par's 1 on a relative axis). Lower
    is better. Returns "" with no line."""
    lines = [ln for ln in lines if len(ln["pts"]) >= 2]
    if not lines:
        return ""
    base = LINES_COMPACT if compact else LINES_FRAME
    fr = Frame(**base)
    target = 4 if compact else 6
    xv = [p["x"] for ln in lines for p in ln["pts"]]
    yv = [p["y"] for ln in lines for p in ln["pts"]] + ([guide["y"]] if guide else [])
    xs = Scale(min(xv), max(xv), fr.left + 14, fr.right - 14, log=x_log, integer=not x_log)
    ticks = sorted({t for t in x_ticks if xs.lo <= t <= xs.hi})
    rows = tick_rows([xs(t) for t in ticks], [x_fmt(t) for t in ticks], TICK_CHAR_W[compact])
    if any(rows):                       # a second row of tick labels: the same plot, 16 units more below it
        fr = Frame(**dict(base, h=base["h"] + 16, bottom=base["bottom"] + 16))
    ys = Scale(min(yv), max(yv), fr.bottom, fr.top, log=y_log, integer=y_integer)
    parts = _axes(fr, xs, ys, x_label + (", log scale" if xs.log else ""), y_label + (", log scale" if ys.log else ""),
                  x_fmt=x_fmt, x_ticks=ticks, target=target, compact=compact, x_rows=rows)
    if guide:
        y = ys(guide["y"])
        parts.append(f'<line class="par-line" x1="{_f(fr.left)}" x2="{_f(fr.right)}" y1="{_f(y)}" y2="{_f(y)}">'
                     f'<title>{_esc(guide["label"])}</title></line>')
    # the names in the margin, pushed apart (computed first: each name is drawn in its line's group)
    ends = sorted(((ys(ln["pts"][-1]["y"]), ln["id"]) for ln in lines))
    spot = dict(zip((i for _, i in ends), _spread([y for y, _ in ends], fr.top + 6, fr.bottom - 4,
                                                    16 if compact else 15)))
    lx = fr.right + 10
    for ln in sorted(lines, key=lambda ln: (KIND_ORDER[ln["kind"]], ln["id"])):     # records drawn last, on top
        cls = {"record": "s-record", "reference": "s-reference", "baseline": "s-baseline"}[ln["kind"]]
        coords = " ".join(f"{_f(xs(p['x']))},{_f(ys(p['y']))}" for p in ln["pts"])
        # (data-line-kind, not data-kind: these marks are one design at several points, not the
        # explorer's one mark per design)
        g = [f'<g class="series" data-line-kind="{_esc(ln["kind"])}" data-id="{_esc(ln["id"])}">'
             f'<g data-tip="{_esc(chr(10).join(ln["tip"]))}"><title>{_esc(" · ".join(ln["tip"]))}</title>'
             f'<polyline class="series-line {cls}" points="{coords}"/>'
             f'<polyline class="series-hit" points="{coords}"/></g>']
        for p in ln["pts"]:
            x, y = xs(p["x"]), ys(p["y"])
            mk = (f'<g class="mark" data-line-kind="{_esc(ln["kind"])}" data-x="{_esc(p["x"])}" '
                  f'data-tip="{_esc(chr(10).join(p["tip"]))}"><title>{_esc(" · ".join(p["tip"]))}</title>'
                  f'<circle class="hit" cx="{_f(x)}" cy="{_f(y)}" r="10"/>'
                  f'{marker(ln["kind"], x, y, ln.get("banned", False), 4)}</g>')
            g.append(f'<a href="{_esc(ln["href"])}" aria-label="{_esc(p["tip"][0])}">{mk}</a>' if ln.get("href") else mk)
        last = ln["pts"][-1]
        x, y, ly = xs(last["x"]), ys(last["y"]), spot[ln["id"]]
        g.append(f'<g class="series-name" data-tip="{_esc(chr(10).join(ln["tip"]))}">'
                 f'<path class="leader" d="M{_f(x + 6)} {_f(y)}L{_f(lx - 4)} {_f(ly - 4)}"/>'
                 f'<text class="lv-name" x="{_f(lx)}" y="{_f(ly)}">{_esc(short(ln["name"], LABEL_CHARS[compact]))}'
                 "</text></g></g>")
        parts.append("".join(g))
    desc = (f"{len(lines)} designs, {y_label} (y) against {x_label} (x), one line each, named on the right; lower is "
            "better. The table under the chart lists the same numbers.")
    return _svg(fr, parts, title, desc, cls="chart lines compact" if compact else "chart lines")


# ---------------------------------------------------------------------------
# bars
# ---------------------------------------------------------------------------

def bar_chart(rows, *, title, unit):
    """Horizontal bars: `rows` are (label, value, note) with value >= 0, drawn
    in the given order. Single series: one colour, no legend."""
    if not rows:
        return ""
    bar, gap, label_w, value_w = 16, 12, 90, 150
    height = len(rows) * (bar + gap) + gap
    x0, x1 = label_w, W - value_w
    top = max(v for _, v, _ in rows) or 1
    parts = []
    for k, (label, value, note) in enumerate(rows):
        y = gap + k * (bar + gap)
        w = (x1 - x0) * value / top
        r = min(4, w / 2)
        # a bar square at the baseline, rounded (4px) at its data end
        d = (f"M{_f(x0)} {_f(y)}H{_f(x0 + w - r)}Q{_f(x0 + w)} {_f(y)} {_f(x0 + w)} {_f(y + r)}"
             f"V{_f(y + bar - r)}Q{_f(x0 + w)} {_f(y + bar)} {_f(x0 + w - r)} {_f(y + bar)}H{_f(x0)}Z")
        parts.append(f'<g class="mark" data-label="{_esc(label)}" data-value="{value}">'
                     f"<title>{_esc(label)}: {value} {_esc(unit)}{_esc(note and ' (' + note + ')')}</title>"
                     f'<text class="tick" x="{_f(x0 - 8)}" y="{_f(y + bar - 4)}" text-anchor="end">{_esc(label)}</text>'
                     + (f'<path class="bar" d="{d}"/>' if w > 0 else "")
                     + f'<text class="value" x="{_f(x0 + w + 8)}" y="{_f(y + bar - 4)}">{value}'
                     f"{_esc(note and '  ' + note)}</text></g>")
    parts.append(f'<line class="axis" x1="{_f(x0)}" x2="{_f(x0)}" y1="{_f(gap / 2)}" y2="{_f(height - gap / 2)}"/>')
    fr = Frame(w=W, h=height)
    return _svg(fr, parts, title, f"{len(rows)} bars; the table beside the chart lists the same numbers.",
                cls="chart bars")
