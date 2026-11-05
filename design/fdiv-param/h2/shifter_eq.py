# exhaustive: original shifter+sticky (reference lines 127-129) vs the 4-stage mux shifter with sticky collection (t0)
bad = 0
for qm in range(4096):
    for sh in range(13):
        for st0 in (0, 1):
            qs = qm >> sh
            st1 = st0 | (((qs << sh) & 0xFFF) != qm)
            # t0
            q1 = (qm >> 1) if sh & 1 else qm
            t1 = (sh & 1) & (qm & 1)
            q2 = (q1 >> 2) if sh & 2 else q1
            t2 = t1 | (((sh >> 1) & 1) & ((q1 & 3) != 0))
            q3 = (q2 >> 4) if sh & 4 else q2
            t3 = t2 | (((sh >> 2) & 1) & ((q2 & 15) != 0))
            qs2 = (q3 >> 8) if sh & 8 else q3
            st1b = st0 | t3 | (((sh >> 3) & 1) & ((q3 & 255) != 0))
            if qs != qs2 or int(st1) != int(st1b):
                bad += 1
print("mismatches:", bad)
