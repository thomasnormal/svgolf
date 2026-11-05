"""The standing of one design against its task's field: the "beats / matches" lines of a record page's dashboard
(site/build.py `record_page`: the Area, Performance and Score cards) and the fitted view of its area-time plot.

Standard library only, pure functions, exact integer arithmetic (no epsilon anywhere). ADVISORY: a standing is
recomputed at every site build from the records of that revision, and is never stored in a record, its hash or the
ranking (the ranking is leaderboard.py's board, defined once).

A point is a dict with
    id        unique
    kind      "record" | "reference" | "baseline"
    player    a record's player (None otherwise)
    area      area in 1e-4 um^2 (int): `ppa.area_e4um2_sky130`, or a clocked score's area_um2 * 10^4
    time      ranked time in ps (int): `ppa.delay_ps_sky130`, or cycles x period_ps on a clocked task
Lower is better on both axes and on the score area x time.

The FIELD of a subject is the task's ranked records (exactly the records the board ranks under the current
flow, each with its sky130 columns) of every player except the subject's own; each player counts once. References
(par) and baselines are never in the field; par is compared separately (`vs_par`). Percentages are rounded DOWN
("beats 100%" only when every other player is beaten), always printed with the counts; ties are exact at the
recorded unit (1e-4 um^2, 1 ps); an empty field has no percentage at all.
"""

import math

AXES = ("area", "time", "score")


def score(p):
    """The ranked combined score, exact: area (1e-4 um^2) x time (ps)."""
    return p["area"] * p["time"]


def value(p, axis):
    return score(p) if axis == "score" else p[axis]


def dominates(a, b):
    """a is at least as good as b on both axes and strictly better on one (ties do not dominate)."""
    return (a["area"] <= b["area"] and a["time"] <= b["time"]
            and (a["area"] < b["area"] or a["time"] < b["time"]))


def same_point(a, b):
    return a["area"] == b["area"] and a["time"] == b["time"]


def field_of(subject, records):
    """{player: [their ranked records]} of every player but the subject's own (a reference or a baseline
    has no player, so every player is in its field)."""
    out = {}
    for r in records:
        if r["kind"] != "record" or r.get("player") is None:
            raise ValueError(f"{r['id']}: only ranked player records can be in a field")
        if subject.get("player") is not None and r["player"] == subject["player"]:
            continue
        out.setdefault(r["player"], []).append(r)
    return out


def pct(k, n):
    """k of n as a whole percentage, rounded DOWN (never 'beats 100%' while someone is better), or None
    when n is 0. A non-zero k that rounds to 0 is reported as the string '<1%' by `pct_text`."""
    if n == 0:
        return None
    return (100 * k) // n


def pct_text(k, n):
    p = pct(k, n)
    if p is None:
        return "–"
    if k > 0 and p == 0:
        return "<1%"
    return f"{p}%"


def axis_standing(subject, field, axis):
    """Per axis (area, time or score): each other player counts once, at their BEST value on that axis (a
    real record of theirs reaches it). beaten: the subject is strictly better; matched: exactly equal;
    behind: strictly worse."""
    s = value(subject, axis)
    beaten = matched = behind = 0
    for recs in field.values():
        best = min(value(r, axis) for r in recs)
        if s < best:
            beaten += 1
        elif s == best:
            matched += 1
        else:
            behind += 1
    n = beaten + matched + behind
    return {"n": n, "beaten": beaten, "matched": matched, "behind": behind,
            "beats_pct": pct(beaten, n), "matches_pct": pct(matched, n),
            "beats_text": pct_text(beaten, n), "matches_text": pct_text(matched, n)}


def board_relation(subject, recs):
    """How the subject stands against ONE other player's ranked records on the (area, time) board:
       ahead     some record of theirs dominates the subject
       beaten    the subject dominates every record of theirs
       level     no record of theirs is better, one is identical, the rest are dominated
       tradeoff  none dominates the subject, one is better on one axis (and worse on the other)"""
    if any(dominates(r, subject) for r in recs):
        return "ahead"
    if all(dominates(subject, r) or same_point(subject, r) for r in recs):
        return "level" if any(same_point(subject, r) for r in recs) else "beaten"
    return "tradeoff"


def board_standing(subject, field):
    c = {"beaten": 0, "level": 0, "tradeoff": 0, "ahead": 0}
    for recs in field.values():
        c[board_relation(subject, recs)] += 1
    n = sum(c.values())
    c.update(n=n, beats_pct=pct(c["beaten"], n), matches_pct=pct(c["level"], n),
             beats_text=pct_text(c["beaten"], n), matches_text=pct_text(c["level"], n))
    return c


def pareto_layers(points):
    """Non-dominated sorting (leaderboard.py's rule on the sky130 axes): layer 1 is the front."""
    remaining, layers = list(points), []
    while remaining:
        front = [p for p in remaining if not any(dominates(o, p) for o in remaining)]
        layers.append(front)
        gone = {id(p) for p in front}
        remaining = [p for p in remaining if id(p) not in gone]
    return layers


def board_position(subject, records):
    """The subject among ALL ranked records (its own player's included: the board's own numbers): its
    Pareto layer and its rank by score (ties share a rank: 1, 1, 3). A subject that is not a record is placed
    where it WOULD be ("would be layer k"); a reference is par and has no board position (None)."""
    if subject["kind"] == "reference":
        return None
    pts = [r for r in records if r["id"] != subject["id"]] + [subject]
    layer = next(k for k, front in enumerate(pareto_layers(pts), 1) if any(p is subject for p in front))
    s = score(subject)
    rank = 1 + sum(1 for r in pts if r is not subject and score(r) < s)
    return {"layer": layer, "rank": rank, "of": len(pts), "hypothetical": subject["kind"] != "record"}


def vs_par(subject, par):
    """Per axis: the exact signed difference to par (delta, in the axis's integer unit) and the relative one
    (rel = delta / par's value, a float, for display only); None without par."""
    if par is None:
        return None
    out = {}
    for axis in AXES:
        a, b = value(subject, axis), value(par, axis)
        out[axis] = {"delta": a - b, "rel": (a - b) / b}
    return out


def among(subject, designs, axis):
    """The subject's place among the designs shown on the page (references, baselines, records; NOT a
    ranking): 1 + the number of designs strictly better, ties sharing a place, and the count."""
    s = value(subject, axis)
    return {"place": 1 + sum(1 for d in designs if d["id"] != subject["id"] and value(d, axis) < s),
            "tied": sum(1 for d in designs if d["id"] != subject["id"] and value(d, axis) == s),
            "of": len(designs)}


def standing(subject, records, par, designs):
    field = field_of(subject, records)
    return {"field_players": len(field), "field_records": sum(len(v) for v in field.values()),
            "axes": {axis: axis_standing(subject, field, axis) for axis in AXES},
            "board": board_standing(subject, field),
            "position": board_position(subject, records),
            "vs_par": vs_par(subject, par),
            "among": {axis: among(subject, designs, axis) for axis in AXES}}


# ------------------------------------------------------------------------------------------- the view

def quantile(sorted_vals, q):
    """Linear interpolation between closest ranks (numpy's default 'linear')."""
    n = len(sorted_vals)
    h = (n - 1) * q
    lo = math.floor(h)
    hi = min(lo + 1, n - 1)
    return sorted_vals[lo] + (h - lo) * (sorted_vals[hi] - sorted_vals[lo])


MIN_FIT = 8          # fewer points than this: show them all
PAD = 0.07           # of the span, on each side


def fit_axis(vals, keep):
    """One axis of the 'fitted to the cluster' view: Tukey fences (Q1 - 1.5 IQR, Q3 + 1.5 IQR) clipped to the
    data, widened to hold every value of `keep` (the subject, par, the front), then padded. Values in the
    display unit (floats)."""
    s = sorted(vals)
    if len(s) >= MIN_FIT:
        q1, q3 = quantile(s, 0.25), quantile(s, 0.75)
        iqr = q3 - q1
        lo, hi = max(s[0], q1 - 1.5 * iqr), min(s[-1], q3 + 1.5 * iqr)
    else:
        lo, hi = s[0], s[-1]
    lo, hi = min([lo] + list(keep)), max([hi] + list(keep))
    span = hi - lo or abs(hi) or 1.0
    return max(0.0, lo - PAD * span), hi + PAD * span


def beyond(points, view):
    """Points outside `view` = (x0, x1, y0, y1), counted per edge (a point past a corner counts on both of its
    edges) and in total (each point once)."""
    x0, x1, y0, y1 = view
    edges = {"left": 0, "right": 0, "below": 0, "above": 0}
    total = 0
    for x, y in points:
        out = False
        if x < x0:
            edges["left"] += 1
            out = True
        elif x > x1:
            edges["right"] += 1
            out = True
        if y < y0:
            edges["below"] += 1
            out = True
        elif y > y1:
            edges["above"] += 1
            out = True
        total += out
    return edges, total
