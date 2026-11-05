#!/usr/bin/env python3.12
"""Test vectors (a, b, want) for fdiv #(W, P): random, exponent-boundary, tie-shaped and corner operands.
want = oracle_int (exact integer RNE), cross-checked against the Fraction oracle on a subset.
usage: gen_vec.py W P N SEED OUT [--frac M]"""
import sys, random, struct
from fdivp_model import oracle_int, oracle_frac, model, model3

def gen(W, P, n, seed):
    rng = random.Random(seed * 1000003 + W * 101 + P)
    K, T = W + P, P - 1
    mW = (1 << W) - 1
    emax = (1 << (W - 1)) - 1
    tm = (1 << T) - 1
    def pat(s, e, f): return (s << (K - 1)) | ((e & mW) << T) | (f & tm)
    def rfrac():
        r = rng.random()
        if r < 0.15: return rng.choice([0, 1, 2, tm, tm - 1, 1 << (T - 1), (1 << (T - 1)) - 1, (1 << (T - 1)) + 1])
        if r < 0.45:   # fraction with a long run of zeros/ones on one side (shape of exact ties and of near-ties)
            k = rng.randrange(0, T + 1)
            f = (rng.getrandbits(max(T - k, 1)) << k) if rng.random() < 0.5 else ((rng.getrandbits(max(T - k, 1)) << k) | ((1 << k) - 1))
            return f & tm
        if r < 0.55:   # a trailing 1000..0
            k = rng.randrange(1, T + 1)
            return ((rng.getrandbits(max(T - k, 1)) << k) | (1 << (k - 1))) & tm
        return rng.getrandbits(T)
    out = []
    ext = sorted(set([0, 1, 2, 3, emax - 2, emax - 1, emax, emax + 1, emax + 2, mW - 3, mW - 2, mW - 1, mW, emax + P, max(emax - P, 0)]))
    ext = [e for e in ext if 0 <= e <= mW]
    for s in (0, 1):
        for e in ext:
            for f in (0, 1, tm, 1 << (T - 1)):
                out.append(pat(s, e, f))
    corners = list(out)
    pairs = [(x, y) for x in corners for y in corners]
    rng.shuffle(pairs)
    pairs = pairs[: max(n // 4, 1000)]
    while len(pairs) < n:
        r = rng.random()
        if r < 0.25:
            pairs.append((rng.getrandbits(K), rng.getrandbits(K)))
        elif r < 0.5:  # normal-range results
            pairs.append((pat(rng.getrandbits(1), emax + rng.randrange(-3, 4), rfrac()), pat(rng.getrandbits(1), emax + rng.randrange(-3, 4), rfrac())))
        elif r < 0.8:  # exponent difference near the underflow / overflow boundaries
            d = rng.choice([-1, 1]) * rng.randrange(max(emax - P - 3, 0), emax + P + 3)
            e1 = rng.randrange(1, mW) if mW > 1 else 1
            e2 = e1 - d
            if not (0 <= e2 <= mW): e1, e2 = (e2 if e2 >= 0 else 0) % (mW + 1), (e1 if e2 < 0 else e2)
            pairs.append((pat(rng.getrandbits(1), e1, rfrac()), pat(rng.getrandbits(1), e2 & mW, rfrac())))
        else:          # divisor a power of two or a subnormal, dividend with tie-shaped fraction
            eb = rng.choice([0, 0, 1, rng.randrange(0, mW + 1)])
            fb = rng.choice([0, 0, 1 << rng.randrange(0, T), rfrac()])
            pairs.append((pat(rng.getrandbits(1), rng.randrange(0, mW + 1), rfrac()), pat(rng.getrandbits(1), eb, fb)))
    return pairs[:n]

if __name__ == '__main__':
    W, P, N, seed = map(int, sys.argv[1:5]); out = sys.argv[5]
    M = int(sys.argv[sys.argv.index('--frac') + 1]) if '--frac' in sys.argv else 2000
    pairs = gen(W, P, N, seed)
    bad = 0
    with open(out, 'wb') as f:
        for i, (a, b) in enumerate(pairs):
            w = oracle_int(W, P, a, b)
            if i < M and oracle_frac(W, P, a, b) != w:
                bad += 1
            f.write(struct.pack('<QQQ', a, b, w))
    print(f'({W},{P}): {len(pairs)} vectors, oracle_int vs Fraction oracle on {min(M, len(pairs))}: {bad} disagreements')
    if '--model' in sys.argv or '--model3' in sys.argv:
        mf = model3 if '--model3' in sys.argv else model
        mm = sum(1 for a, b in pairs if mf(W, P, a, b) != oracle_int(W, P, a, b))
        print('python model vs oracle_int mismatches:', mm)
