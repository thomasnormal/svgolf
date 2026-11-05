"""The counter fixture's own evaluator (task.json `oracle`; the clocked post-synthesis check, PLAN4
Gate 2 step 4, binding check (ii)), independent of ls-sv: Python integers only.

- `txns(params, seed, count)`: the stimulus entries after the checker's reset entries, each a dict
  of the inputs but the clock ({"rst", "en"}): `en` = 1 seven times in eight (so N = 8 wraps), and
  one entry in 32 a reset.
- `expect(params, entries)`: per entry, the outputs SeqTask claims in its snapshot ({"q": q}), or
  None before the first reset entry: a reset restarts q at 0, any other entry adds `en` mod 2^N.
"""
import random


def txns(params, seed, count=24):
    rng = random.Random(seed * 1000003 + int(params["N"]))
    return [{"rst": int(rng.getrandbits(5) == 0), "en": int(rng.getrandbits(3) != 0)}
            for _ in range(max(count, 320))]


def expect(params, entries):
    n, q, out = int(params["N"]), None, []
    for e in entries:
        q = 0 if e["rst"] else None if q is None else (q + e["en"]) % (1 << n)
        out.append(None if q is None else {"q": q})
    return out
