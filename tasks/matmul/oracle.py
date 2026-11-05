"""Transaction oracle of task `matmul` (README.md, "The oracle"; task.json `oracle`).

The task's OWN evaluator: Python integers only, independent of ls-sv. It is NOT part of the trusted
statement (`Spec.lean` and `SvGolf/TaskSeq.lean` are). The clocked post-synthesis check (PLAN4.md,
Gate 2 step 4) uses it as binding check (ii): in every cycle where the netlist shows `done` = 1, its
`C` must be `good` for the transaction being held, so a bug that a design shares with ls-sv is
still caught. It is reviewed with the spec (REVIEW.md, "The oracle").

`params` maps "N", "W", "AccW" to ints (each >= 1, and N*N*W, N*N*AccW < 2^31: C10). Matrices are
FLAT ints, as the ports carry them: entry (i, k) of A is bits [(i*N+k)*W, (i*N+k+1)*W), two's
complement, least significant entry first; B likewise; entry (i, j) of C is bits
[(i*N+j)*AccW, (i*N+j+1)*AccW).

- `product(N, W, AccW, a, b)`: the flat C = A.B: signed W-bit entries, exact integer dot products,
  each reduced mod 2^AccW. It transcribes `Spec.lean`'s `product`.
- `good(params, txn, result)`: True iff `result["C"]` is the product of the transaction's operands.
- `mismatch(params, txn, result)`: None, or the first wrong entry in words, for reports.
- `txns(params, seed, count=24)`: a deterministic list of transactions (below).
- `oracle(params, inputs)`: the comb tasks' shape (`check/postsynth.py`, `load_oracle`):
  {"C": product} for inputs {"A": .., "B": ..}.

A transaction is a dict:
- "A", "B": the operands. The checker drives them from the start entry through the entry whose
  edge first shows `done` = 1 (the hold of C2).
- "gap": how many entries with `start` = 0 come before this transaction's start. For the first
  transaction it counts from the reset release; for the others, from the entry right after the
  snapshot where the previous transaction's `done` first shows 1. So 0 is the earliest start the
  rely allows: the first entry after the release, or back-to-back (C2).
- "free": `gap` dicts {"A", "B"}, the operand values for those gap entries. They are known but
  arbitrary, and the claim ignores them (CONTRACT.md, point 3). A design that reads A or B outside
  the hold shows it in C.
- "tag": a name for reports.

Every list starts with eight corner transactions: zero; all-min times all-min, the largest
positive dot product N * 2^(2W-2), which wraps once it reaches 2^(AccW-1); min times max, the most
negative; max times max; all -1; the identity on each side; a min/max checkerboard. The zero
transaction comes first, the others in a seeded order. Its gap, the idle time after the release,
is 0, 1 or N + 3 for seed mod 3 = 0, 1, 2 (gap 0 starts at the release itself). The rest are
random: a quarter of the entries come from the extremes {min, max, -1, 0, 1}, the others are
uniform. Half the gaps are 0
(back-to-back), and one in eight is N + 3, a hold longer than the reference's latency. Only
`random.Random.getrandbits` is used, whose output for an int seed is stable across CPython
versions.

`python3 oracle.py` runs the self-test: Spec.lean's examples, a second formulation of the product,
the generator's coverage, and that the transactions tell apart the wrong arithmetic of the planned
attack designs (Gate 3 step 4).
"""

import random

PARAMS = ("N", "W", "AccW")


def _point(params):
    n, w, accw = (int(params[k]) for k in PARAMS)
    if min(n, w, accw) < 1 or n * n * w >= 1 << 31 or n * n * accw >= 1 << 31:
        raise ValueError(f"matmul: point {params} is out of range (Spec.lean `task.inRange`)")
    return n, w, accw


def entries(w, x, count):
    """The `count` signed `w`-bit entries of the flat int `x`, entry 0 first."""
    mask, half = (1 << w) - 1, 1 << (w - 1)
    return [((x >> (idx * w)) & mask ^ half) - half for idx in range(count)]


def pack(w, vals):
    """The flat int whose entry idx is `vals[idx]` mod 2^w (two's complement)."""
    return sum((v % (1 << w)) << (idx * w) for idx, v in enumerate(vals))


def product(n, w, accw, a, b):
    """`Spec.lean`'s `product n w accw a b`: C[i][j] = sum_k A[i][k] B[k][j] mod 2^accw, flat."""
    ea, eb = entries(w, a, n * n), entries(w, b, n * n)
    c = 0
    for i in range(n):
        for j in range(n):
            s = sum(ea[i * n + k] * eb[k * n + j] for k in range(n))
            c |= (s % (1 << accw)) << ((i * n + j) * accw)
    return c


def oracle(params, inputs):
    n, w, accw = _point(params)
    return {"C": product(n, w, accw, inputs["A"], inputs["B"])}


def good(params, txn, result):
    n, w, accw = _point(params)
    got = result.get("C") if isinstance(result, dict) else None
    if not isinstance(got, int) or isinstance(got, bool):
        return False
    return got == product(n, w, accw, txn["A"], txn["B"])


def mismatch(params, txn, result):
    if good(params, txn, result):
        return None
    n, w, accw = _point(params)
    got = result.get("C") if isinstance(result, dict) else None
    if not isinstance(got, int) or isinstance(got, bool):
        return f"no integer C in {result!r}"
    if got >> (n * n * accw):
        return f"C = {got:#x} has bits above its {n * n * accw}-bit width"
    want = entries(accw, product(n, w, accw, txn["A"], txn["B"]), n * n)
    have = entries(accw, got, n * n)
    ij = next(ij for ij in range(n * n) if want[ij] != have[ij])
    return (f"C[{ij // n}][{ij % n}] = {have[ij]}, want {want[ij]} (signed {accw}-bit; "
            f"transaction {txn.get('tag', '?')})")


# ---------------------------------------------------------------------------
# the transaction generator
# ---------------------------------------------------------------------------

def _below(rng, m):
    """Uniform in [0, m), from `getrandbits` only (stable across CPython versions)."""
    k = m.bit_length()
    while True:
        r = rng.getrandbits(k)
        if r < m:
            return r


def _signed(w, u):
    half = 1 << (w - 1)
    return (u ^ half) - half


def txns(params, seed, count=24):
    n, w, accw = _point(params)
    big = 1000003
    rng = random.Random(((seed * big + n) * big + w) * big + accw)
    lo, hi, nn = -(1 << (w - 1)), (1 << (w - 1)) - 1, n * n
    extremes = sorted({lo, hi, -1, 0, 1 if w >= 2 else 0})
    unit = 1 if w >= 2 else -1   # the identity's diagonal; 1 is not a 1-bit signed value

    def mixed():
        return [extremes[_below(rng, len(extremes))] if _below(rng, 4) == 0
                else _signed(w, rng.getrandbits(w)) for _ in range(nn)]

    def checker(x, y):
        return [x if (i + k) % 2 == 0 else y for i in range(n) for k in range(n)]

    ident = [unit if i == k else 0 for i in range(n) for k in range(n)]
    corners = [("zero", [0] * nn, [0] * nn), ("min*min", [lo] * nn, [lo] * nn),
               ("min*max", [lo] * nn, [hi] * nn), ("max*max", [hi] * nn, [hi] * nn),
               ("-1*-1", [-1] * nn, [-1] * nn), ("I*rand", ident, mixed()),
               ("rand*I", mixed(), ident), ("checker", checker(lo, hi), checker(hi, lo))]
    for t in range(len(corners) - 1, 1, -1):       # the first stays first; shuffle the rest
        u = 1 + _below(rng, t)
        corners[t], corners[u] = corners[u], corners[t]
    gaps = [(0, 1, n + 3)[seed % 3], 0, 0, 1, 0, 2, 0, n + 3]
    plan = [(tag, a, b, g) for (tag, a, b), g in zip(corners, gaps)]
    while len(plan) < count:
        r = _below(rng, 8)
        plan.append(("rand", mixed(), mixed(), 0 if r < 4 else 1 if r < 6 else 2 if r < 7 else n + 3))
    out = []
    for tag, a, b, g in plan[:count]:
        free = [{"A": rng.getrandbits(nn * w), "B": rng.getrandbits(nn * w)} for _ in range(g)]
        out.append({"A": pack(w, a), "B": pack(w, b), "gap": g, "free": free, "tag": tag})
    return out


# ---------------------------------------------------------------------------
# self-test
# ---------------------------------------------------------------------------

PROBE_POINTS = [(1, 1, 1), (2, 3, 5), (3, 4, 8), (4, 8, 32)]   # task.json `probe_points`
POSTSYNTH_POINTS = [(2, 4, 8), (4, 8, 32)]                      # task.json `postsynth.points`


def _product_alt(n, w, accw, a, b):
    """A second formulation: k outermost, sign by subtraction, one reduction at the end."""
    acc = [0] * (n * n)
    for k in range(n):
        for i in range(n):
            for j in range(n):
                x = (a >> ((i * n + k) * w)) % (1 << w)
                y = (b >> ((k * n + j) * w)) % (1 << w)
                x -= (x >> (w - 1)) << w
                y -= (y >> (w - 1)) << w
                acc[i * n + j] += x * y
    return sum((v % 2 ** accw) * 2 ** (ij * accw) for ij, v in enumerate(acc))


def _faults(n, w, accw):
    """The wrong arithmetic of the planned attack designs (PLAN4.md Gate 3 step 4), each as a
    function of (a, b) -> flat C, with the condition under which it differs from the product."""
    m, nn = 1 << accw, n * n

    def gen(term, ks=range(n), out=lambda i, j: (i, j)):
        def f(a, b):
            ea, eb = entries(w, a, nn), entries(w, b, nn)
            c = 0
            for i in range(n):
                for j in range(n):
                    s = sum(term(ea[i * n + k], eb[k * n + j]) for k in ks)
                    oi, oj = out(i, j)
                    c |= (s % m) << ((oi * n + oj) * accw)
            return c
        return f

    def unsigned(x, y):
        return (x % (1 << w)) * (y % (1 << w))

    def no_sign_ext(x, y):
        return (x * y) % (1 << (2 * w))

    def trunc_2w(a, b):      # a 2W-bit accumulator, sign-extended to AccW
        return pack(accw, entries(2 * w, product(n, w, 2 * w, a, b), nn))

    return [
        ("unsigned product", gen(unsigned), accw > w >= 2),
        ("missing sign extension", gen(no_sign_ext), accw > 2 * w),
        ("accumulator truncated to 2W", trunc_2w, accw > 2 * w),
        ("off-by-one k (last step lost)", gen(lambda x, y: x * y, range(n - 1)), True),
        ("off-by-one k (first step lost)", gen(lambda x, y: x * y, range(1, n)), True),
        ("B.A instead of A.B", lambda a, b: product(n, w, accw, b, a), n >= 2),
        ("C transposed", gen(lambda x, y: x * y, out=lambda i, j: (j, i)), n >= 2),
    ]


def self_test(seeds=range(5)):
    """Raise AssertionError on the first failure; return a one-line summary."""
    # Spec.lean's examples (proved there by `decide`)
    assert product(2, 4, 8, 0x432F, 0x0765) == 0x122BFA09
    assert product(1, 4, 8, 0x8, 0x8) == 0x40 and product(1, 4, 6, 0x8, 0x8) == 0
    # the first one in matrix form: [[-1,2],[3,4]] . [[5,6],[7,0]] = [[9,-6],[43,18]]
    assert pack(4, [-1, 2, 3, 4]) == 0x432F and pack(4, [5, 6, 7, 0]) == 0x0765
    assert entries(8, 0x122BFA09, 4) == [9, -6, 43, 18]
    # hand examples at the edges: W = 1 entries are 0 and -1; AccW = 1 is the parity
    assert product(1, 1, 1, 1, 1) == 1 and product(1, 1, 3, 1, 1) == 1
    assert product(2, 1, 2, 0b1111, 0b1111) == 0b10101010         # every entry (-1)(-1)+(-1)(-1) = 2
    assert product(2, 1, 1, 0b1111, 0b1111) == 0                   # ... = 0 mod 2
    assert product(1, 8, 32, 0x80, 0x7F) == (-128 * 127) % 2 ** 32
    assert oracle({"N": 2, "W": 4, "AccW": 8}, {"A": 0x432F, "B": 0x0765}) == {"C": 0x122BFA09}
    # out of range is refused, never answered
    for bad in ({"N": 0, "W": 1, "AccW": 1}, {"N": 1, "W": 0, "AccW": 1}, {"N": 1 << 16, "W": 1, "AccW": 1}):
        try:
            _point(bad)
            raise AssertionError(f"{bad} accepted")
        except ValueError:
            pass
    total = 0
    for (n, w, accw) in sorted(set(PROBE_POINTS + POSTSYNTH_POINTS)):
        params = {"N": n, "W": w, "AccW": accw}
        lo, hi, nn = -(1 << (w - 1)), (1 << (w - 1)) - 1, n * n
        faults = _faults(n, w, accw)
        for seed in seeds:
            ts = txns(params, seed)
            assert ts == txns(params, seed), "txns is not deterministic"
            assert len(ts) == 24 and ts[0]["tag"] == "zero" and ts[0]["gap"] == (0, 1, n + 3)[seed % 3]
            total += len(ts)
            seen, prev, stale = set(), 0, None
            for idx, t in enumerate(ts):
                assert 0 <= t["A"] < 1 << (nn * w) and 0 <= t["B"] < 1 << (nn * w)
                assert len(t["free"]) == t["gap"] and all(
                    0 <= f[p] < 1 << (nn * w) for f in t["free"] for p in "AB")
                c = product(n, w, accw, t["A"], t["B"])
                assert c == _product_alt(n, w, accw, t["A"], t["B"])
                assert good(params, t, {"C": c}) and mismatch(params, t, {"C": c}) is None
                assert not good(params, t, {"C": c ^ 1}) and mismatch(params, t, {"C": c ^ 1})
                assert not good(params, t, {"C": c | 1 << (nn * accw)}) and not good(params, t, {})
                vals = set(entries(w, t["A"], nn)) | set(entries(w, t["B"], nn))
                seen |= {("lo", lo in vals), ("hi", hi in vals)}
                if t["gap"] == 0 and idx > 0 and prev != 0:
                    seen.add("back-to-back after a nonzero result")
                if t["gap"] >= 1:
                    seen.add("gap")
                if t["gap"] > n + 1:
                    seen.add("hold longer than N + 1")
                # an accumulator not cleared on start (only by reset): C_t = C_(t-1) + P_t
                cu = entries(accw, c, nn)
                stale = cu if stale is None else [s + v for s, v in zip(stale, cu)]
                seen.add(("stale caught", pack(accw, stale) != c))
                prev = c
            for want in (("lo", True), ("hi", True), "back-to-back after a nonzero result", "gap",
                         "hold longer than N + 1", ("stale caught", True)):
                assert want in seen, f"{params} seed {seed}: no transaction with {want}"
            if (n, w, accw) in POSTSYNTH_POINTS:
                for name, f, differs in faults:
                    if differs:
                        assert any(not good(params, t, {"C": f(t["A"], t["B"])}) for t in ts), \
                            f"{params} seed {seed}: no transaction catches the {name}"
    assert txns({"N": 4, "W": 8, "AccW": 32}, 0) != txns({"N": 4, "W": 8, "AccW": 32}, 1)
    return (f"matmul oracle self-test: ok ({len(set(PROBE_POINTS + POSTSYNTH_POINTS))} points x "
            f"{len(seeds)} seeds, {total} transactions; every planned arithmetic fault caught at "
            f"{POSTSYNTH_POINTS})")


if __name__ == "__main__":
    print(self_test())
