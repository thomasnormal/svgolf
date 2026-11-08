"""Reactive oracle of task `arbiter` (task.json `oracle`): the stimulus and the executable reading of the
guarantee, for check.py's clocked post-synthesis check of the reactive kind (`react-family`).

The task's OWN evaluator, in Python integers, independent of ls-sv. It is NOT part of the trusted
statement (`Spec.lean` and `SvGolf/TaskReact.lean`'s `ReactTask` are). The clocked post-synthesis check
uses it as its binding check (ii): on every segment of the run (a reset entry, then the entries with
`rst` = 0 up to the next reset entry), the grants the SCORED NETLIST shows must meet G0 to G4, so a
wrong design that ls-sv agrees with is still caught (attack A17, a time bomb, is the reason for long
reset-free segments).

`params` maps "N" to an int (1 <= N, N*N < 2^31). Request and grant vectors are N-bit ints, bit i =
client i.

- `segments(params, rng, count, long)`: the stimulus of one seed (below).
- `violations(params, reset_out, entries, outs)`: the guarantee on ONE segment, as a list of
  (j, why): `reset_out` is the reset entry's snapshot ({"gnt": int}), `entries[j]` the data inputs
  of entry j after the release ({"req": int}), `outs[j]` its snapshot. j = -1 is the reset
  snapshot. Empty: the segment meets G0 (the reset snapshot's gnt = 0), G1 (at most one grant),
  G2 (only to requesters), G3 (someone if anyone requests) and G4 (a client requesting at the N
  entries j..j+N-1 is granted in one of those snapshots; K = N - 1, Spec.lean `Statement`).
  `grant_violations(params, reset_gnt, reqs, gnts)` is the same on plain int lists.
- `oracle(params, inputs)`: None. A reactive task has no function of one input vector; the loader
  of the combinational smoke check asks for the name only.

A segment is a dict:
- "tag": the request pattern, for reports;
- "reset": the data inputs of the segment's reset entry, {"req": int} (known: the statement asks
  for it, and every net computed from `req` must be known in the reset snapshot);
- "entries": the data inputs of the entries after the release, until the next segment's reset
  entry, [{"req": int}, ...].

`segments` gives `count` segments; the last is `long` entries long (reset-free), a concatenation of
blocks of the patterns below, so a design that changes its behaviour after many cycles (a counter,
a time bomb) is driven past it under contention. The others are short (1 to 6N entries, N - 1, N
and N + 1 included: the edges of G4's window), one pattern each: `random` (each client requests
with probability 3/4), `sparse` (1/4), `all` (every client, always), `none`, `hold` (a request,
once raised, stays up for a random time around 2N: persistent requesters), `pair` (two clients
always, the others random), `single` (one client at a time), `intermittent` (client 0 every
other entry, the others always: the legal starving case, Spec.lean "does NOT pin"). Only
`random.Random.getrandbits` is used, whose output is stable across CPython versions; the CHECKER
seeds the generator (with $SVGOLF_POSTSYNTH_SALT, check/postsynth.py), so a secret salt makes the
stimulus unpredictable.

`python3 oracle.py` runs the self-test.
"""

import random

PATTERNS = ("random", "sparse", "all", "none", "hold", "pair", "single", "intermittent")


def _n(params):
    n = int(params["N"])
    if n < 1 or n * n >= 1 << 31:
        raise ValueError(f"arbiter: point {params} is out of range (Spec.lean `task.inRange`)")
    return n


def _below(rng, m):
    """Uniform in [0, m), from `getrandbits` only (stable across CPython versions)."""
    if m <= 1:
        return 0
    k = m.bit_length()
    while True:
        r = rng.getrandbits(k)
        if r < m:
            return r


def _bern(rng, num, den):
    return _below(rng, den) < num


def _pattern(rng, n, tag, length, state):
    """`length` request vectors of pattern `tag`; `state` carries `hold`'s and `single`'s runs over
    consecutive calls (the long segment's blocks)."""
    full = (1 << n) - 1
    out = []
    for j in range(length):
        if tag == "random":
            v = sum(1 << i for i in range(n) if _bern(rng, 3, 4))
        elif tag == "sparse":
            v = sum(1 << i for i in range(n) if _bern(rng, 1, 4))
        elif tag == "all":
            v = full
        elif tag == "none":
            v = 0
        elif tag == "hold":
            left = state.setdefault("left", [0] * n)
            for i in range(n):
                if left[i] > 0:
                    left[i] -= 1
                elif _bern(rng, 1, 2):
                    left[i] = 1 + _below(rng, 4 * n)       # raised: held this many entries more
            v = sum(1 << i for i in range(n) if left[i] > 0)
        elif tag == "pair":
            if "pair" not in state:
                a = _below(rng, n)
                state["pair"] = (a, (a + 1 + _below(rng, n - 1)) % n if n > 1 else a)
            a, b = state["pair"]
            v = (1 << a) | (1 << b) | sum(1 << i for i in range(n) if _bern(rng, 1, 2))
        elif tag == "single":
            if state.get("run", 0) <= 0:
                state["one"], state["run"] = _below(rng, n), 1 + _below(rng, 2 * n)
            state["run"] -= 1
            v = 1 << state["one"]
        elif tag == "intermittent":
            v = (full & ~1) | (1 if j % 2 else 0)
        else:
            raise ValueError(tag)
        out.append(v)
    return out


def segments(params, rng, count, long):
    """The stimulus of one seed: `count` segments, the last `long` entries long (module docstring)."""
    n = _n(params)
    full = (1 << n) - 1
    lengths = [1, max(1, n - 1), n, n + 1, 2 * n, 3 * n]
    out = []
    for k in range(max(0, count - 1)):
        tag = PATTERNS[k % len(PATTERNS)] if k < len(PATTERNS) else PATTERNS[_below(rng, len(PATTERNS))]
        length = lengths[_below(rng, len(lengths))] if _bern(rng, 1, 2) else 1 + _below(rng, 6 * n)
        out.append((tag, rng.getrandbits(n) & full, _pattern(rng, n, tag, length, {})))
    if count >= 1:
        reqs, state = [], {}
        while len(reqs) < long:
            tag = ("random", "all", "hold", "pair", "sparse")[_below(rng, 5)]
            reqs += _pattern(rng, n, tag, min(long - len(reqs), 1 + _below(rng, 64 * n)), state)
        out.append((f"long ({long} entries)", rng.getrandbits(n) & full, reqs))
    return [{"tag": tag, "reset": {"req": r0}, "entries": [{"req": r} for r in reqs]} for tag, r0, reqs in out]


def _bits(v, n):
    return [i for i in range(n) if v >> i & 1]


def violations(params, reset_out, entries, outs, limit=20):
    """The guarantee on one segment (module docstring): [(j, why)], at most `limit` entries."""
    return grant_violations(params, reset_out["gnt"], [e["req"] for e in entries], [o["gnt"] for o in outs],
                            limit)


def grant_violations(params, reset_gnt, reqs, gnts, limit=20):
    """`violations` on int lists: the reset snapshot's grant, the requests, the grants."""
    n = _n(params)
    k = n - 1
    if len(gnts) != len(reqs):
        raise ValueError(f"{len(gnts)} grants for {len(reqs)} requests")
    bad = []
    if reset_gnt != 0:
        bad.append((-1, f"G0: the reset snapshot shows gnt = {reset_gnt:#x}, not 0"))
    miss = [0] * n                       # consecutive entries client i requested, ungranted
    for j, (r, g) in enumerate(zip(reqs, gnts)):
        if g & (g - 1):
            bad.append((j, f"G1: gnt = {g:#x} grants clients {_bits(g, n)}"))
        if g & ~r:
            bad.append((j, f"G2: gnt = {g:#x} grants clients {_bits(g & ~r, n)}, which do not request "
                        f"(req = {r:#x})"))
        if r and not g:
            bad.append((j, f"G3: req = {r:#x}, nobody is granted"))
        for i in range(n):
            if r >> i & 1 and not g >> i & 1:
                miss[i] += 1
                if miss[i] > k:
                    bad.append((j, f"G4: client {i} requested at the {n} entries {j - k}..{j} and was "
                                f"granted in none of their snapshots"))
                    miss[i] = 0
            else:
                miss[i] = 0
        if len(bad) >= limit:
            break
    return bad[:limit]


def oracle(params, inputs):
    return None


# ---------------------------------------------------------------- self-test

def _rr(n, reqs):
    """A mask round-robin (tasks/arbiter/reference/rr_mask.sv), in Python."""
    mask, out = (1 << n) - 1, []
    for r in reqs:
        m = r & mask
        p = (m & -m) if m else (r & -r)
        if p:
            mask = ~((p << 1) - 1) & ((1 << n) - 1)
        out.append(p)
    return out


def _fixed(n, reqs):
    return [r & -r for r in reqs]


def self_test():
    for n in (1, 2, 3, 5, 8):
        for seed in range(3):
            rng = random.Random(seed * 1000 + n)
            segs = segments({"N": n}, rng, 12, 300)
            assert len(segs) == 12 and len(segs[-1]["entries"]) == 300, (n, seed)
            assert all(set(e) == {"req"} and 0 <= e["req"] < 1 << n
                       for s in segs for e in s["entries"] + [s["reset"]])
            assert {s["tag"] for s in segs[:len(PATTERNS)]} == set(PATTERNS)
            for s in segs:
                reqs = [e["req"] for e in s["entries"]]
                v = violations({"N": n}, {"gnt": 0}, s["entries"], [{"gnt": g} for g in _rr(n, reqs)])
                assert not v, (n, s["tag"], v[:2])
            rng2 = random.Random(seed * 1000 + n)
            assert segments({"N": n}, rng2, 12, 300) == segs          # deterministic for a seed
    # the wrong designs fail, each on its own clause
    gv = grant_violations
    allr = [7] * 6
    assert gv({"N": 3}, 0, allr, _fixed(3, allr))[0][1].startswith("G4"), "fixed priority starves"
    assert gv({"N": 3}, 0, allr, allr)[0][1].startswith("G1"), "grant everyone"
    assert gv({"N": 3}, 0, [0, 2], [0, 1])[0][1].startswith("G2"), "a spurious grant"
    assert gv({"N": 3}, 0, [2], [0])[0][1].startswith("G3"), "nobody granted"
    assert gv({"N": 3}, 1, [], [])[0][1].startswith("G0"), "a grant out of reset"
    # the bound is exact: N - 1 misses are allowed, N are not
    assert not gv({"N": 3}, 0, [3, 3, 2], [1, 1, 2])          # client 1 waits 2 = N - 1
    assert gv({"N": 3}, 0, [2, 2, 2], [0, 0, 0])               # G3 and G4
    assert [w for _, w in gv({"N": 3}, 0, [3, 3, 3, 3], [1, 1, 1, 2])
            if w.startswith("G4")], "client 1 ungranted at 3 = N entries"
    # N = 1: K = 0, so a request must be granted in its own snapshot
    assert not gv({"N": 1}, 0, [1, 0, 1], [1, 0, 1]) and gv({"N": 1}, 0, [1], [0])
    # the intermittent requester of the round-robin starves, legally (no G4 window of N requests)
    reqs = _pattern(random.Random(1), 3, "intermittent", 40, {})
    assert not gv({"N": 3}, 0, reqs, _rr(3, reqs))
    print("arbiter oracle: self-test ok")


if __name__ == "__main__":
    self_test()
