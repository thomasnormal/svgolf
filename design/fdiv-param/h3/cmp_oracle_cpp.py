import sys, subprocess, struct
from fdivp_model import oracle_int, oracle_frac
import numpy as np
bad = 0
for K in range(4, 10):
    for W in range(2, K - 1):
        P = K - W
        fn = f'/tmp/od_{W}_{P}.bin'
        subprocess.run(['./oracle_dump', str(W), str(P), fn], check=True)
        arr = np.fromfile(fn, dtype=np.uint32)
        n = 1 << K
        mism = 0
        step = 1 if K <= 7 else 7   # python oracle on a stride for the larger ones
        for a in range(0, n):
            for b in range(0, n, step):
                if int(arr[a * n + b]) != oracle_int(W, P, a, b): mism += 1
        print(W, P, 'C++ vs python oracle_int mismatches', mism, flush=True)
        bad += mism
print('total', bad)
