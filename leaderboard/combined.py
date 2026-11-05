"""svGolf's combined score: the area-time product, defined once.

    ADP = sky130 area (um^2) x time (ps)

`area` is the ranked sky130 area of the scored netlist (flow A0', `sky130_a0_v3`: the pinned `abc -g`
netlist, each gate one sky130 `_1` cell, repaired by buffering; flops included on a clocked task).
`time` is the critical-path delay on a combinational task (`delay_ps_sky130`, every input driven by
the task's input drive, default `sky130_fd_sc_hd__buf_8`) and `cycles` x the
register-to-register period on a clocked one (check.py's clocked `time_ps`). Lower is better.

The exact value is an integer in 1e-4 um^2 x ps (the area is recorded in 1e-4 um^2, the time in
whole ps), so two scores compare exactly; it is shown in um^2 x ns (`um2ns`), the display unit
`UNIT`. Used by the site (site/build.py: the big numbers, the score chart, the leaderboard order)
and importable by leaderboard.py (`of_record`). Standard library only, no side effects.
"""

UNIT = "µm²·ns"                 # the display unit (um^2 x ns)
UNIT_ASCII = "um2*ns"
NAME = "area × time"


def time_ps(*, delay_ps=None, cycles=None, period_ps=None):
    """The time a score multiplies: the delay of a combinational design, `cycles` x `period_ps` of a
    clocked one; None when it cannot be known."""
    if cycles is not None or period_ps is not None:
        if not (_nat(cycles) and _nat(period_ps)):
            return None
        return cycles * period_ps
    return delay_ps if _nat(delay_ps) else None


def exact(area_e4um2, time):
    """The exact score: area in 1e-4 um^2 times time in ps (an int), or None if either is missing."""
    if not (_nat(area_e4um2) and _nat(time)):
        return None
    return area_e4um2 * time


def um2ns(score):
    """An exact score in the display unit, um^2 x ns (a float), or None."""
    return None if score is None else score / 10_000_000


def e4um2(area_um2):
    """An area in um^2 (a float, as a clocked check result writes it) as integer 1e-4 um^2."""
    return None if area_um2 is None else int(round(area_um2 * 10_000))


def of_columns(*, area_e4um2=None, area_um2=None, delay_ps=None, cycles=None, period_ps=None, time=None):
    """The exact score of a design's sky130 columns, whichever form they come in, or None."""
    a = area_e4um2 if area_e4um2 is not None else e4um2(area_um2)
    t = time if time is not None else time_ps(delay_ps=delay_ps, cycles=cycles, period_ps=period_ps)
    return exact(a, t)


def of_record(rec):
    """The exact score of a leaderboard record, or None if it has no sky130 columns: a clocked record
    scores `area_um2` x `time_ps` (check.py's ranked pair), a combinational one its `ppa` block's
    `area_e4um2_sky130` x `delay_ps_sky130`."""
    s = rec.get("score") or {}
    if "time_ps" in s and "area_um2" in s:
        return of_columns(area_um2=s["area_um2"], time=s["time_ps"])
    p = rec.get("ppa")
    if isinstance(p, dict) and p.get("available") is True:
        return of_columns(area_e4um2=p.get("area_e4um2_sky130"), delay_ps=p.get("delay_ps_sky130"))
    return None


def fmt(value):
    """A score (um^2 x ns, a float) as text: whole units from 1000 up, in thin-space groups from
    10 000 ('1198', '52 339'), four significant digits below ('118.4', '3.57')."""
    if value is None:
        return "–"
    if value >= 10000:
        return f"{round(value):,}".replace(",", " ")
    if value >= 1000:
        return f"{round(value)}"
    return f"{value:.4g}" if value >= 1 else f"{value:.3g}"


def _nat(v):
    return isinstance(v, int) and not isinstance(v, bool) and v >= 0
