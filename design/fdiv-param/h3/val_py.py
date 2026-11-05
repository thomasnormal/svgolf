import sys, itertools, random, time
from multiprocessing import Pool
from fdivp_model import model, oracle_int, oracle_frac, consts

def run(args):
    W, P, mode = args
    K = W + P
    n = 1 << K
    bad_m = bad_o = 0
    ex = []
    pairs = itertools.product(range(n), range(n)) if mode == 'all' else (
        (random.Random(W * 100 + P + i).randrange(n), random.Random(W * 1000 + P + 7 * i).randrange(n)) for i in range(mode))
    cnt = 0
    for a, b in pairs:
        cnt += 1
        m = model(W, P, a, b)
        oi = oracle_int(W, P, a, b)
        if m != oi:
            bad_m += 1
            if len(ex) < 3: ex.append((a, b, m, oi))
        if mode != 'all' or K <= 8:
            of = oracle_frac(W, P, a, b)
            if of != oi:
                bad_o += 1
                if len(ex) < 6: ex.append(('ORACLE', a, b, oi, of))
    return (W, P, cnt, bad_m, bad_o, ex)

if __name__ == '__main__':
    Kmax = int(sys.argv[1])
    jobs = [(W, K - W, 'all') for K in range(4, Kmax + 1) for W in range(2, K - 1)]
    t = time.time()
    with Pool(12) as p:
        for r in p.imap_unordered(run, jobs):
            print(r, flush=True)
    print('done', time.time() - t)
