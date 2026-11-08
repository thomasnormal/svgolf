"""Transaction oracle of task `sorter` (README.md, "The oracle"; task.json `oracle`).

The task's OWN evaluator: Python integers and `sorted()`, independent of ls-sv. It is NOT part of the
trusted statement (`Spec.lean` and `SvGolf/TaskSeq.lean`'s `StreamTask` are). A clocked
post-synthesis check uses it as its binding check (ii): the values a netlist emits on the cycles
with `out_valid` = 1, from one start to the next, must be `good` for that transaction, so a bug
that a design shares with ls-sv is still caught. Reviewed with the spec (REVIEW.md, "The oracle").

`params` maps "N", "W" to ints (each >= 1, N*W < 2^31: C10). Values are unsigned W-bit ints.

- `sort_asc(xs)`: Spec.lean's `sortAsc`, transcribed (insertAsc folded from the right).
- `good(params, txn, result)`: True iff `result["out"]`, the emitted values in order, is
  `sorted(txn["xs"])`: ascending, duplicates kept, nothing missing or extra.
- `mismatch(params, txn, result)`: None, or what is wrong in words, for reports.
- `txns(params, seed, count=24, rng=None)`: a deterministic list of transactions (below); `rng`: the checker's random source for the seed (check/postsynth.py `seed_draw`: derived from $SVGOLF_POSTSYNTH_SALT, F5, 2026-11-07); None: the deterministic one of (seed, params), for this file's self-test and the simulations.
- `oracle(params, inputs)`: the comb tasks' loader shape: {"out": sorted} for {"xs": ..}.

A transaction is a dict:
- "xs": the N values, driven on `in_data` with `in_valid` = 1 at the N entries after the start.
- "gap": how many entries with `start` = 0 come before this transaction's start: for the first
  transaction from the reset release, for the others from the entry right after the snapshot that
  shows the previous transaction's N-th output (StreamTask.Idle). So 0 is the earliest start the
  rely allows: the release itself, or back-to-back (C2, CONTRACT.md point 7).
- "free": known, arbitrary W-bit values for `in_data` on this transaction's entries with
  `in_valid` = 0 (its gap entries, its start entry, the entries waiting for its outputs), used in
  order and cyclically. The claim ignores them; a design that reads in_data there shows it.
- "tag": a name for reports.

Every list starts with ten corner transactions: all 0; all 2^W - 1; all equal (a middle value);
already ascending; descending; 0 and 2^W - 1 alternating; one 2^W - 1 among 0s; one 0 among
2^W - 1s; ascending with a duplicate pair; and two values each repeated (few distinct values).
The first stays first; the rest are shuffled. The first gap, the idle time after the release, is
0, 1 or 2N + 3 for seed mod 3 = 0, 1, 2. The rest are random: a quarter of the values come from
the extremes {0, 1, 2^W - 2, 2^W - 1}, the others are uniform (duplicates are frequent at small W).
Half the gaps are 0 (back-to-back), and one in eight is 2N + 3. Only `random.Random.getrandbits`
is used, whose output for an int seed is stable across CPython versions.

`python3 oracle.py` runs the self-test.
"""

import random

PARAMS = ("N", "W")


def _point(params):
    n, w = (int(params[k]) for k in PARAMS)
    if min(n, w) < 1 or n * w >= 1 << 31:
        raise ValueError(f"sorter: point {params} is out of range (Spec.lean `task.inRange`)")
    return n, w


def sort_asc(xs):
    """Spec.lean's `sortAsc`: insertAsc a (sortAsc as), insertAsc placing a before the first b it
    is <= to (unsigned)."""
    out = []
    for a in reversed(xs):
        k = next((i for i, b in enumerate(out) if a <= b), len(out))
        out.insert(k, a)
    return out


def oracle(params, inputs):
    _point(params)
    return {"out": sorted(inputs["xs"])}


def mismatch(params, txn, result):
    n, w = _point(params)
    got = result.get("out") if isinstance(result, dict) else None
    if not isinstance(got, list) or not all(isinstance(v, int) and not isinstance(v, bool) for v in got):
        return f"no list of int values in {result!r}"
    if any(not 0 <= v < 1 << w for v in got):
        return f"a value outside [0, 2^{w}) in {got}"
    want = sorted(txn["xs"])
    if len(got) != len(want):
        return f"{len(got)} values emitted, want {len(want)} (transaction {txn.get('tag', '?')})"
    if got != want:
        k = next(k for k in range(n) if got[k] != want[k])
        return f"output {k} is {got[k]}, want {want[k]} (transaction {txn.get('tag', '?')})"
    return None


def good(params, txn, result):
    return mismatch(params, txn, result) is None


def _below(rng, m):
    """Uniform in [0, m), from `getrandbits` only (stable across CPython versions)."""
    k = m.bit_length()
    while True:
        r = rng.getrandbits(k)
        if r < m:
            return r


def txns(params, seed, count=24, rng=None):
    n, w = _point(params)
    big = 1000003
    if rng is None:
        rng = random.Random((seed * big + n) * big + w)
    top = (1 << w) - 1
    extremes = sorted({0, 1, max(top - 1, 0), top})
    mid = top // 2 + (rng.getrandbits(w) % 2 if w > 1 else 0)
    asc = sorted(rng.getrandbits(w) for _ in range(n))
    pair = [rng.getrandbits(w), rng.getrandbits(w)]
    corners = [("zeros", [0] * n), ("ones", [top] * n), ("equal", [mid] * n), ("ascending", asc),
               ("descending", asc[::-1]), ("alternating", [(0, top)[i % 2] for i in range(n)]),
               ("one max", [top if i == n // 2 else 0 for i in range(n)]),
               ("one zero", [0 if i == n - 1 else top for i in range(n)]),
               ("ascending dup", sorted(asc[:1] + asc[:n - 1])),
               ("two values", [pair[i % 2] for i in range(n)])]
    for t in range(len(corners) - 1, 1, -1):       # the first stays first; shuffle the rest
        u = 1 + _below(rng, t)
        corners[t], corners[u] = corners[u], corners[t]
    gaps = [(0, 1, 2 * n + 3)[seed % 3], 0, 0, 1, 0, 2, 0, 2 * n + 3, 0, 1]
    plan = [(tag, xs, g) for (tag, xs), g in zip(corners, gaps)]
    while len(plan) < count:
        xs = [extremes[_below(rng, len(extremes))] if _below(rng, 4) == 0 else rng.getrandbits(w)
              for _ in range(n)]
        r = _below(rng, 8)
        plan.append(("rand", xs, 0 if r < 4 else 1 if r < 6 else 2 if r < 7 else 2 * n + 3))
    return [{"xs": xs, "gap": g, "free": [rng.getrandbits(w) for _ in range(g + 2 * n + 4)],
             "tag": tag} for tag, xs, g in plan[:count]]


PROBE_POINTS = [(1, 1), (1, 8), (2, 1), (2, 4), (3, 1), (3, 4), (4, 8), (8, 8)]  # task.json
POSTSYNTH_POINTS = [(3, 4), (8, 8)]


def self_test(seeds=range(5)):
    """Raise AssertionError on the first failure; return a one-line summary."""
    assert sort_asc([3, 15, 0, 3, 8]) == [0, 3, 3, 8, 15]          # Spec.lean's example
    assert oracle({"N": 5, "W": 4}, {"xs": [3, 15, 0, 3, 8]}) == {"out": [0, 3, 3, 8, 15]}
    for bad in ({"N": 0, "W": 1}, {"N": 1, "W": 0}, {"N": 1 << 16, "W": 1 << 15}):
        try:
            _point(bad)
            raise AssertionError(f"{bad} accepted")
        except ValueError:
            pass
    total = 0
    for n, w in PROBE_POINTS:
        params, top = {"N": n, "W": w}, (1 << w) - 1
        for seed in seeds:
            ts = txns(params, seed)
            assert ts == txns(params, seed), "txns is not deterministic"
            assert len(ts) == 24 and ts[0]["tag"] == "zeros" and ts[0]["gap"] == (0, 1, 2 * n + 3)[seed % 3]
            total += len(ts)
            seen = set()
            for t in ts:
                xs = t["xs"]
                assert len(xs) == n and all(0 <= v <= top for v in xs + t["free"])
                assert len(t["free"]) == t["gap"] + 2 * n + 4
                s = sorted(xs)
                assert s == sort_asc(xs) and good(params, t, {"out": s})
                assert not good(params, t, {"out": s[:-1]}) and not good(params, t, {"out": s + [0]})
                assert not good(params, t, {"out": [top + 1] + s[1:]}) and not good(params, t, {})
                if len(set(xs)) < n:
                    seen.add("duplicate")
                    assert not good(params, t, {"out": sorted(set(xs))})      # a dropped duplicate
                if n > 1 and s != s[::-1]:
                    seen.add("unequal")
                    assert not good(params, t, {"out": s[::-1]})
                seen |= {("zero", 0 in xs), ("top", top in xs), ("gap0", t["gap"] == 0),
                         ("long gap", t["gap"] > 2 * n), ("gap", t["gap"] >= 1)}
                if n > 1 and xs == s and len(set(xs)) > 1:
                    seen.add("sorted input")
                if n > 1 and xs == s[::-1] and len(set(xs)) > 1:
                    seen.add("reverse input")
            want = [("zero", True), ("top", True), ("gap0", True), ("long gap", True), ("gap", True)]
            if n > 1:
                want += ["duplicate", "unequal"] + (["sorted input", "reverse input"] if w > 1 else [])
            for x in want:
                assert x in seen, f"{params} seed {seed}: no transaction with {x}"
    assert txns({"N": 8, "W": 8}, 0) != txns({"N": 8, "W": 8}, 1)
    return (f"sorter oracle self-test: ok ({len(PROBE_POINTS)} points x {len(seeds)} seeds, "
            f"{total} transactions)")


if __name__ == "__main__":
    print(self_test())
