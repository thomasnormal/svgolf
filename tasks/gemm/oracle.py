"""Oracle of task `gemm` (README.md; task.json `oracle`): the software model of the task.

The task's OWN evaluator, Python integers only. It states, and the exploration check (check/explore.py) uses:

- the arithmetic: `reference(job, W, X)`, the exact sums and the output stage `scale` (`oracle(params, inputs)`
  is the same in the shape every task's oracle has);
- the memory: `image(W, lgn, lge, layout)`, the beats the external memory holds for a job under the
  canonical layout or an entry's declared one (`check_layout` refuses a malformed declaration);
- the stimulus: `jobs(point, seed, shape, rng, data_rng, data_shift)`, a deterministic job list with corner cases
  (and the `sweep` list: one job per shift 0..63, each with data and a multiplier under which that shift's results
  are inside the clamp), and `stalls(seed, n, rng, nominal)`, the environment's pauses on every channel;
- the protocol's legal timings and the results: `check_trace(point, jobs, images, events)`, which reads the
  events the environment (env/tb.sv) records and returns what is wrong in words, or nothing;
- the steady-state cycle count: `job_period(events)`; and `control_trace(events)`, what two runs on different
  data must agree on (data-independence).

A point is {"LGE": log2 of the entries per beat, "LAT": the burst latency}. E = 2^LGE; a beat is 16*E bits,
entry k in bits [16k+15:16k].

A job is a dict: "lgn" (N = 2^lgn, LGE <= lgn <= LGE+5), "batch" (>= 1), "mul" (M, 0..65535), "shift"
(s, 0..63), "zp", "lo", "hi" (0..65535, lo <= hi), and for the stimulus "W" (N rows of N signed 16-bit ints),
"X" (batch vectors of N unsigned 16-bit ints) and "tag".

    sum[i][b] = sum_j W[i][j] * X[b][j]                         (exact)
    r         = floor((sum*M + 2^(s-1)) / 2^s) if s >= 1 else sum*M
    Y[b][i]   = min(max(r + zp, lo), hi)

`python3 oracle.py` runs the self-test.
"""
import random

MAX_SCALE = 5            # N <= 32 E
JOB_FIELDS = ("lgn", "batch", "mul", "shift", "zp", "lo", "hi")
CHANNELS = ("job", "rq", "rd", "x", "y")      # the stall word's bits, in order


def entries(point):
    return 1 << point["LGE"]


def legal_job(point, job):
    """None, or why `job` is not a job the environment may offer at `point`."""
    lge = point["LGE"]
    if not lge <= job["lgn"] <= lge + MAX_SCALE:
        return f"lgn {job['lgn']} outside {lge}..{lge + MAX_SCALE}"
    if not 1 <= job["batch"] <= 65535:
        return f"batch {job['batch']} outside 1..65535"
    if not (0 <= job["mul"] < 1 << 16 and 0 <= job["shift"] < 64):
        return "mul or shift out of range"
    if not 0 <= job["lo"] <= job["hi"] < 1 << 16 or not 0 <= job["zp"] < 1 << 16:
        return "zp, lo, hi must be 16-bit with lo <= hi"
    return None


def scale(acc, job):
    """The output stage on one exact sum."""
    p = acc * job["mul"]
    s = job["shift"]
    r = (p + (1 << (s - 1))) >> s if s else p          # Python's >> is the floor
    return min(max(r + job["zp"], job["lo"]), job["hi"])


def sums(W, X):
    """The exact sums: sums(W, X)[b][i] = sum_j W[i][j] * X[b][j]. (A zero weight adds nothing and is skipped: the
    scored job with identity weights, 4096 x 4096 x 4096, is then 2^24 products.)"""
    rows = [[(j, w) for j, w in enumerate(row) if w] for row in W]
    return [[sum(w * vec[j] for j, w in row) for row in rows] for vec in X]


def reference(job, W=None, X=None):
    """Y[b][i] for the job (its own W and X when none are given)."""
    W, X = job["W"] if W is None else W, job["X"] if X is None else X
    return [[scale(a, job) for a in vec] for vec in sums(W, X)]


def oracle(params, inputs):
    """The loader shape every task's oracle has: {"Y": the results} of one job, `inputs` the job's fields with its
    "W" and "X" (`params` is the point; the arithmetic does not depend on it)."""
    return {"Y": reference(inputs)}


# ----------------------------------------------------------------------------------------------- the memory image
def canonical_layout():
    """The layout of an entry that declares none: the matrix itself (one segment, level 0, coefficient 1),
    in E x E tiles, 16 bits per entry."""
    return {"default": [{"level": 0, "terms": [[0, 0, 1]], "bits": 16, "tile": 0}]}


def check_layout(layout):
    """None, or why `layout` (an entry's declaration) is not one. A layout maps a scale q = lgn - LGE ("0".."5",
    or "default") to a list of segments {"level", "terms": [[block row, block column, coefficient], ...],
    "bits" (16..32), "tile" (log2 of the tile side over E; default 0)}."""
    if not isinstance(layout, dict) or not layout:
        return "a layout is an object {scale or \"default\": [segments]}"
    for key, segs in layout.items():
        if key != "default" and key not in {str(q) for q in range(MAX_SCALE + 1)}:
            return f"layout key {key!r} is not a scale 0..{MAX_SCALE} or \"default\""
        if not isinstance(segs, list) or not segs:
            return f"layout[{key!r}] is not a non-empty list of segments"
        for seg in segs:
            if not isinstance(seg, dict) or set(seg) - {"level", "terms", "bits", "tile"}:
                return f"layout[{key!r}]: a segment has the keys level, terms, bits, tile"
            lvl, bits, tile = seg.get("level"), seg.get("bits", 16), seg.get("tile", 0)
            if not (isinstance(lvl, int) and 0 <= lvl <= MAX_SCALE and isinstance(bits, int) and 16 <= bits <= 32
                    and isinstance(tile, int) and 0 <= tile <= MAX_SCALE):
                return f"layout[{key!r}]: level 0..{MAX_SCALE}, bits 16..32, tile 0..{MAX_SCALE}"
            if key != "default" and lvl + tile > int(key):
                return f"layout[{key!r}]: a block of level {lvl} is smaller than a tile of side E*2^{tile}"
            terms = seg.get("terms")
            if not isinstance(terms, list) or not terms:
                return f"layout[{key!r}]: a segment needs terms"
            for t in terms:
                if not (isinstance(t, list) and len(t) == 3 and all(isinstance(v, int) for v in t)
                        and 0 <= t[0] < 1 << lvl and 0 <= t[1] < 1 << lvl and t[2] != 0 and abs(t[2]) <= 255):
                    return f"layout[{key!r}]: a term is [block row, block column, nonzero coefficient]"
            lo, hi = combination_range(terms)
            if lo < -(1 << (bits - 1)) or hi > (1 << (bits - 1)) - 1:
                return (f"layout[{key!r}]: a combination with these coefficients reaches {lo} .. {hi} on 16-bit "
                        f"weights, which does not fit its {bits} signed bits")
    return None


def combination_range(terms):
    """The least and the largest value of sum_k c_k * w_k over signed 16-bit weights (a block named twice adds its
    coefficients)."""
    coef = {}
    for bi, bj, c in terms:
        coef[(bi, bj)] = coef.get((bi, bj), 0) + c
    pos = sum(c for c in coef.values() if c > 0)
    neg = sum(-c for c in coef.values() if c < 0)
    return -32768 * pos - 32767 * neg, 32767 * pos + 32768 * neg


def segments(layout, q):
    """The segments of `layout` at scale q (None: the canonical layout)."""
    layout = layout or canonical_layout()
    segs = layout.get(str(q), layout.get("default"))
    if segs is None:
        raise ValueError(f"the layout has no segments for scale {q} and no default")
    for seg in segs:
        if seg["level"] + seg.get("tile", 0) > q:
            raise ValueError(f"at scale {q} a level-{seg['level']} block is smaller than its tile")
    return segs


def segment_matrix(W, seg):
    """The matrix a segment stores: sum of coefficient * block."""
    n = len(W)
    h = n >> seg["level"]
    out = [[0] * h for _ in range(h)]
    for bi, bj, c in seg["terms"]:
        for i in range(h):
            row, src = out[i], W[bi * h + i]
            for j in range(h):
                row[j] += c * src[bj * h + j]
    return out


def image(W, lgn, lge, layout=None):
    """The beats (ints of 16*E bits) of the external memory for weights W under `layout`.

    Per segment, tile by tile (tile-major, tiles of side E*2^tile): the low 16 bits of every entry, row-major,
    E entries per beat; then, when bits > 16, the upper bits - 16 bits of every entry, row-major, packed from
    bit 0 of a beat and padded with zeros to a whole beat. A stored value that does not fit `bits` signed bits
    is an error of the layout."""
    e, q = 1 << lge, lgn - lge
    memw, beats = 16 * e, []
    for seg in segments(layout, q):
        S, bits = segment_matrix(W, seg), seg.get("bits", 16)
        t = e << seg.get("tile", 0)
        lo, hi = -(1 << (bits - 1)), (1 << (bits - 1)) - 1
        for tr in range(0, len(S), t):
            for tc in range(0, len(S), t):
                upper, nup = 0, 0
                for i in range(t):
                    row = S[tr + i][tc:tc + t]
                    for v in row:
                        if not lo <= v <= hi:
                            raise ValueError(f"layout: the value {v} does not fit {bits} signed bits")
                    for k in range(0, t, e):
                        beat = 0
                        for m, v in enumerate(row[k:k + e]):
                            beat |= (v & 0xFFFF) << (16 * m)
                        beats.append(beat)
                    if bits > 16:
                        for v in row:
                            upper |= ((v >> 16) & ((1 << (bits - 16)) - 1)) << nup
                            nup += bits - 16
                if bits > 16:
                    for k in range(0, nup, memw):
                        beats.append((upper >> k) & ((1 << memw) - 1))
    return beats


def x_beats(job, lge):
    """The activation stream of a job: vector by vector, N/E beats each."""
    e, out = 1 << lge, []
    for vec in job["X"]:
        for k in range(0, len(vec), e):
            beat = 0
            for m, v in enumerate(vec[k:k + e]):
                beat |= v << (16 * m)
            out.append(beat)
    return out


def y_beats(job, lge):
    """{(vector, beat in vector): the result beat} of a job."""
    e, out = 1 << lge, {}
    for b, vec in enumerate(reference(job)):
        for r in range(len(vec) // e):
            beat = 0
            for m, v in enumerate(vec[r * e:(r + 1) * e]):
                beat |= v << (16 * m)
            out[(b, r)] = beat
    return out


# ------------------------------------------------------------------------------------------------- the stimulus
W_CORNERS = (-32768, 32767, -1, 0, 1)
X_CORNERS = (0, 1, 65535, 32768, 32767)


def data_small(rng, m):
    """A value in 0 .. m-1 (m <= 8)."""
    return rng.getrandbits(8) % m


def _matrix(rng, n, kind):
    if kind == "max":                     # the largest sums: every product at its extreme
        return [[-32768] * n for _ in range(n)]
    if kind == "identity":
        return [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    if kind == "small":                   # sums near zero, of both signs: the rounding shows
        return [[data_small(rng, 5) - 2 for _ in range(n)] for _ in range(n)]
    out = []
    for _ in range(n):
        row = []
        for _ in range(n):
            r = rng.getrandbits(4)
            row.append(W_CORNERS[rng.getrandbits(8) % 5] if r < 3 else rng.getrandbits(16) - 32768)
        out.append(row)
    return out


def _vectors(rng, n, batch, kind):
    if kind == "max":
        return [[65535] * n for _ in range(batch)]
    if kind == "small":
        return [[data_small(rng, 4) for _ in range(n)] for _ in range(batch)]
    out = []
    for _ in range(batch):
        vec = []
        for _ in range(n):
            r = rng.getrandbits(4)
            vec.append(X_CORNERS[rng.getrandbits(8) % 5] if r < 3 else rng.getrandbits(16))
        out.append(vec)
    return out


KINDS = ("max", "identity", "small", "random")
SWEEP = "sweep"
SWEEP_BIG = range(45, 55)            # the shifts whose results need the largest sums: the sweep's jobs of N = 32 E


def sweep_shape():
    """The shape `sweep`: 64 jobs of one vector, job s at shift s (a triple (q, batch, s))."""
    return [(MAX_SCALE if s in SWEEP_BIG else 0, 1, s) for s in range(64)]


def sum_bits(kind, lgn):
    """About how many bits the sums of a job of `kind` data have (max: exactly 2^(31 + lgn), less 2^(15 + lgn))."""
    return {"max": 31 + lgn, "identity": 16, "small": 2 + lgn // 2, "random": 30 + lgn // 2}[kind]


def shift_job(rng, s, lgn, seed):
    """The data kind and the layer parameters of a sweep job at shift `s`: data whose sums, times a multiplier of
    1 to 16 bits, shifted right by s, land inside 16 bits wherever legal data can (small or identity data for the
    short shifts, random for the middle ones, the extreme sums for the long ones; above about 2^(47 + lgn) every
    legal sum rounds to 0 and the result is the clamped zero point, which is what the job then checks)."""
    kind = ("identity" if seed % 2 == 0 else "small") if s < 17 else "random" if s < 45 else "max"
    want = 6 + rng.getrandbits(3)                                   # result bits aimed at: 6..13
    mb = min(16, max(1, s + want - sum_bits(kind, lgn)))
    mul = (1 << (mb - 1)) | rng.getrandbits(mb - 1)
    zp = rng.getrandbits(8) if kind == "identity" else 32768 - rng.getrandbits(8)
    return kind, {"mul": mul, "shift": s, "zp": zp, "lo": 0, "hi": 65535}


def jobs(point, seed, shape=None, rng=None, data_rng=None, data_shift=0):
    """A deterministic list of jobs at `point`.

    `shape`: a list of (scale q, batch) pairs, one per job (None: a default list that grows with the seed), or
    of triples (q, batch, s) that fix the job's shift (`shift_job`), or the word `sweep` (`sweep_shape`).
    `rng` draws the layer parameters (M, s, zp, lo, hi) and `data_rng` the weights and activations: two runs
    with the same `rng` and different `data_rng` are the two runs of the data-independence check, and
    `data_shift` = 1 gives every job data of ANOTHER kind under the same parameters (identity weights against
    small ones, the extreme sums against identity, ...), so that a schedule keyed on a pattern both data sets
    would share is seen. Both sources default to deterministic ones of (seed, point). Only `getrandbits` is
    used (stable across CPython versions)."""
    lge = point["LGE"]
    rng = rng or random.Random(f"gemm-ctl-{seed}-{lge}-{point['LAT']}")
    data_rng = data_rng or random.Random(f"gemm-data-{seed}-{lge}-{point['LAT']}")
    if shape is None:
        shape = [(0, 1), (1, 3), (0, 2), (2, 5)] if seed % 2 == 0 else [(1, 1), (0, 4), (2, 2), (1, 7)]
    if shape == SWEEP:
        shape = sweep_shape()
    out = []
    for k, (q, batch, *fixed) in enumerate(shape):
        n = 1 << (lge + q)
        kind = KINDS[(k + seed) % 4]
        if fixed:                         # a job at a given shift
            kind, par = shift_job(rng, fixed[0], lge + q, seed)
        elif kind == "max":               # the sums as they are, clamped to the full range
            par = {"mul": 1, "shift": 0, "zp": 0, "lo": 0, "hi": 65535}
        elif kind == "identity":          # the activations pass through unchanged
            par = {"mul": 1, "shift": 0, "zp": 0, "lo": 0, "hi": 65535}
        elif kind == "small":             # small sums, a small odd multiplier and a short shift: halves, both signs
            par = {"mul": 1 + 2 * (rng.getrandbits(8) % 4), "shift": 1 + rng.getrandbits(8) % 3,
                   "zp": 1000 + rng.getrandbits(8), "lo": 0, "hi": 65535}
        else:
            # typical results inside the 16-bit range (a sum is around 2^(29.5 + lgn/2), M around 2^15), a wide
            # clamp; now and then a tight clamp, an extreme multiplier or an extreme shift
            odd = rng.getrandbits(3)
            lo, hi = rng.getrandbits(13), 65535 - rng.getrandbits(13)
            if odd == 0:
                lo = rng.getrandbits(16)
                hi = min(65535, lo + rng.getrandbits(8))
            shift = 32 + (lge + q) // 2 + rng.getrandbits(1)
            if odd == 1:
                shift = (0, 63, 1)[rng.getrandbits(8) % 3]
            mul = 16384 + rng.getrandbits(15)
            if odd == 2:
                mul = (1, 65535, 0)[rng.getrandbits(8) % 3]
            par = {"mul": mul, "shift": shift, "zp": 16384 + rng.getrandbits(15), "lo": lo, "hi": hi}
        job = {"lgn": lge + q, "batch": batch, **par,
               "tag": f"{kind}-q{q}-b{batch}" + (f"-s{fixed[0]}" if fixed else "")}
        kind = KINDS[(KINDS.index(kind) + data_shift) % 4]         # the data's kind (the parameters stay)
        job["W"] = _matrix(data_rng, n, kind)
        job["X"] = _vectors(data_rng, n, batch, kind)
        if kind == "max" and data_rng.getrandbits(1):      # the other extreme sign
            job["W"] = [[32767] * n for _ in range(n)]
        out.append(job)
    return out


def stalls(seed, n=4096, rng=None, nominal=False):
    """The environment's pauses: n words, bit k = 1 pauses channel CHANNELS[k] in a cycle (job_valid, rq_ready,
    rd_valid, x_valid, y_ready), read cyclically. `nominal`: no pause anywhere (the scored timing)."""
    if nominal:
        return [0] * n
    rng = rng or random.Random(f"gemm-stall-{seed}")
    dens = [(0, 1, 2, 3, 6)[rng.getrandbits(8) % 5] for _ in CHANNELS]    # per channel: pause 0/8 .. 6/8 of the time
    out = []
    for _ in range(n):
        w = 0
        for k, d in enumerate(dens):
            if rng.getrandbits(3) < d:
                w |= 1 << k
        out.append(w)
    return out


# --------------------------------------------------------------------------------------------------- the trace
def parse_trace(text):
    """The events env/tb.sv writes, one per line:
       J cyc k                          job k accepted
       Q cyc addr len                   request accepted
       D cyc                            memory beat transferred
       X cyc                            activation beat transferred
       Y cyc vec row data               result beat transferred (data in hex)
       S cyc bits addr len vec row      the design's control outputs changed (bits: job_ready rq_valid
                                        rd_ready x_ready y_valid, then the request and result positions)
       E cyc words...                   a protocol violation the environment saw
       F cyc                            every expected result arrived (the run's last line)
       T cyc                            the run timed out
    """
    out = []
    for line in text.splitlines():
        p = line.split()
        if not p:
            continue
        if p[0] in "JQDXFT":
            out.append((p[0], int(p[1]), *map(int, p[2:])))
        elif p[0] == "Y":
            out.append(("Y", int(p[1]), int(p[2]), int(p[3]), int(p[4], 16)))
        elif p[0] == "S":
            out.append(("S", int(p[1]), p[2], *map(int, p[3:])))
        else:
            out.append((p[0], int(p[1]) if len(p) > 1 and p[1].isdigit() else -1, " ".join(p[2:])))
    return out


def check_trace(point, job_list, images, events):
    """What is wrong with a run, in words (an empty list: nothing).

    The results: every (vector, beat) of every job exactly once, job after job, with the reference's data. The
    design's side of the protocol: every requested beat inside the current job's image, a length of at least 1
    (the environment also reports a valid or a payload dropped before its transfer, as `E` events). The
    environment's side (a check of the testbench itself): the first beat of a burst no earlier than LAT cycles
    after its request, one burst at a time."""
    lge, lat = point["LGE"], point["LAT"]
    bad = [f"cycle {e[1]}: {e[2]}" for e in events if e[0] == "E"]
    if any(e[0] == "T" for e in events):
        bad.append(f"timeout at cycle {[e[1] for e in events if e[0] == 'T'][0]}: not every result arrived")
    elif not any(e[0] == "F" for e in events):
        bad.append("the run did not finish (no end marker)")
    want = [y_beats(j, lge) for j in job_list]
    got = [dict() for _ in job_list]
    cur_job, out_job, burst = -1, 0, None
    for e in events:
        if e[0] == "J":
            cur_job = e[2]
        elif e[0] == "Q":
            _, cyc, addr, length = e
            if burst is not None and burst[1] > 0:
                bad.append(f"cycle {cyc}: testbench: a request accepted while a burst is outstanding")
            if cur_job < 0:
                bad.append(f"cycle {cyc}: a memory request before any job was accepted")
            elif length < 1 or addr + length > len(images[cur_job]):
                bad.append(f"cycle {cyc}: request of {length} beats at {addr} leaves job {cur_job}'s image "
                           f"({len(images[cur_job])} beats)")
            burst = [cyc, length, True]
        elif e[0] == "D":
            if burst is None or burst[1] <= 0:
                bad.append(f"cycle {e[1]}: testbench: a memory beat without a burst")
            else:
                if burst[2] and e[1] < burst[0] + lat:
                    bad.append(f"cycle {e[1]}: testbench: first beat {e[1] - burst[0]} cycles after the request "
                               f"(LAT = {lat})")
                burst[1] -= 1
                burst[2] = False
        elif e[0] == "Y":
            _, cyc, vec, row, data = e
            while out_job < len(job_list) and len(got[out_job]) == len(want[out_job]):
                out_job += 1
            if out_job >= len(job_list):
                bad.append(f"cycle {cyc}: a result beat after every job's results")
                continue
            if (vec, row) not in want[out_job]:
                bad.append(f"cycle {cyc}: result position (vector {vec}, beat {row}) is not one of job {out_job}")
            elif (vec, row) in got[out_job]:
                bad.append(f"cycle {cyc}: result (vector {vec}, beat {row}) of job {out_job} sent twice")
            else:
                got[out_job][(vec, row)] = data
                if data != want[out_job][(vec, row)]:
                    e_ = 1 << lge
                    k = next(m for m in range(e_) if (data >> 16 * m) & 0xFFFF != (want[out_job][(vec, row)] >> 16 * m) & 0xFFFF)
                    bad.append(f"cycle {cyc}: job {out_job} ({job_list[out_job].get('tag', '')}) vector {vec} row "
                               f"{row * e_ + k}: got {(data >> 16 * k) & 0xFFFF}, the reference is "
                               f"{(want[out_job][(vec, row)] >> 16 * k) & 0xFFFF}")
    for k, (g, w) in enumerate(zip(got, want)):
        if len(g) != len(w) and not any(e[0] == "T" for e in events):
            bad.append(f"job {k}: {len(w) - len(g)} of {len(w)} result beats never arrived")
    return bad


def control_trace(events):
    """What must not depend on the data: every event with its cycle, the result beats without their data."""
    return [e[:4] if e[0] == "Y" else e for e in events]


def job_period(events, job_list, lge):
    """The cycles between the last result beats of consecutive jobs: a list, one per job after the first."""
    ends, k, left = [], 0, None
    for e in events:
        if e[0] != "Y":
            continue
        if left is None:
            left = job_list[k]["batch"] << (job_list[k]["lgn"] - lge)
        left -= 1
        if left == 0:
            ends.append(e[1])
            k += 1
            left = None
            if k == len(job_list):
                break
    return [b - a for a, b in zip(ends, ends[1:])]


# ------------------------------------------------------------------------------------------------- the self-test
def _selftest():
    job = {"mul": 3, "shift": 2, "zp": 10, "lo": 0, "hi": 65535}
    assert scale(5, job) == 14 and scale(-5, job) == 6 and scale(-1 << 46, job) == 0      # 3.75 -> 4, -3.75 -> -4
    assert scale(2, dict(job, shift=2, mul=1)) == 11 and scale(-2, dict(job, shift=2, mul=1)) == 10   # halves round up
    assert scale(7, dict(job, shift=0)) == 31 and scale(1 << 46, dict(job, shift=63)) == 10
    assert scale(1 << 40, dict(job, hi=77)) == 77 and scale(-9, dict(job, lo=12)) == 12
    W = [[1, -2], [3, 4]]
    assert sums(W, [[5, 6], [1, 0]]) == [[-7, 39], [1, 3]]
    pt = {"LGE": 1, "LAT": 2}
    assert image([[1, -2], [3, 4]], 1, 1) == [1 | (0xFFFE << 16), 3 | (4 << 16)]
    # a declared layout: the four quadrants' sum at 18 bits, then the matrix itself
    W4 = [[30000, 30000, -30000, 1], [2, 3, 4, 5], [30000, 30000, -30000, -1], [6, 7, 8, 9]]
    lay = {"1": [{"level": 1, "terms": [[0, 0, 1], [0, 1, 1], [1, 0, 1], [1, 1, 1]], "bits": 18},
                 {"level": 0, "terms": [[0, 0, 1]], "bits": 16}], "0": canonical_layout()["default"]}
    assert check_layout(lay) is None and check_layout({"7": []}) and check_layout({"0": [{"level": 1, "terms": [[0, 0, 1]]}]})
    img = image(W4, 2, 1, lay)
    s00 = 30000 - 30000 + 30000 - 30000
    s01, s10, s11 = 30000 + 1 + 30000 - 1, 2 + 4 + 6 + 8, 3 + 5 + 7 + 9
    assert img[0] == (s00 & 0xFFFF) | ((s01 & 0xFFFF) << 16) and img[1] == s10 | (s11 << 16)
    assert img[2] == ((s00 >> 16) & 3) | (((s01 >> 16) & 3) << 2) and len(img) == 3 + 8
    assert img[3] == 30000 | (30000 << 16)          # the level-0 segment: tile (0, 0), row 0
    try:
        image(W4, 2, 1, {"default": [{"level": 1, "terms": [[0, 0, 4]], "bits": 16}]})
        raise AssertionError("an overflowing layout was accepted")
    except ValueError:
        pass
    seen = [0, 0]                           # results strictly inside the clamp, of the jobs with a wide clamp
    for seed in range(8):
        for j in jobs({"LGE": 2, "LAT": 3}, seed):
            assert legal_job({"LGE": 2, "LAT": 3}, j) is None, j["tag"]
            n = 1 << j["lgn"]
            assert len(j["W"]) == n and len(j["X"]) == j["batch"] and len(x_beats(j, 2)) == j["batch"] * n // 4
            ys = [v for vec in reference(j) for v in vec]
            assert all(0 <= v < 65536 for v in ys)
            if j["tag"].startswith(("small", "random")) and j["shift"] not in (0, 1, 63) and j["mul"] > 1 \
                    and j["hi"] - j["lo"] > 4096:
                seen[0] += sum(1 for v in ys if j["lo"] < v < j["hi"])
                seen[1] += len(ys)
    assert 4 * seen[0] >= 3 * seen[1] > 0, seen      # the stimulus exercises the unclamped range
    assert check_layout({"default": [{"level": 0, "terms": [[0, 0, 2]], "bits": 16}]})          # can overflow: refused
    assert check_layout({"default": [{"level": 1, "terms": [[0, 0, 1], [1, 1, 1]], "bits": 16}]})
    assert check_layout({"default": [{"level": 1, "terms": [[0, 0, 1], [1, 1, -1]], "bits": 17}]}) is None
    assert combination_range([[0, 0, 1], [1, 1, -1]]) == (-65535, 65535)
    assert sums([[0, 3], [0, 0]], [[7, 5]]) == [[15, 0]]
    # the sweep: one job per shift; for every shift up to 54 some result is strictly inside the clamp and not the
    # bare zero point (the shift's own bits show), with data of both parities
    for seed in (0, 1):
        sw = jobs({"LGE": 2, "LAT": 3}, seed, SWEEP)
        assert [j["shift"] for j in sw] == list(range(64)) and all(legal_job({"LGE": 2, "LAT": 3}, j) is None for j in sw)
        for j in sw[:55]:
            ys = {v for vec in reference(j) for v in vec}
            assert any(j["lo"] < v < j["hi"] and v != j["zp"] for v in ys), (seed, j["tag"], sorted(ys)[:8])
    # the second data set of the independence check: the same parameters, data of another kind for every job
    a, b = jobs(pt, 0), jobs(pt, 0, data_rng=random.Random(1), data_shift=1)
    assert [[j[f] for f in JOB_FIELDS] for j in a] == [[j[f] for f in JOB_FIELDS] for j in b]
    assert all(x["W"] != y["W"] for x, y in zip(a, b)) and [j["tag"] for j in a] == [j["tag"] for j in b]
    a, b = jobs(pt, 0), jobs(pt, 0, data_rng=random.Random(1))
    assert [[j[f] for f in JOB_FIELDS] for j in a] == [[j[f] for f in JOB_FIELDS] for j in b]
    assert any(x["W"] != y["W"] for x, y in zip(a, b))
    j = jobs(pt, 0)[:1]
    ev = [("J", 5, 0), ("Q", 6, 0, 2), ("D", 8), ("D", 9)]
    ev += [("Y", 20 + k, v, r, d) for k, ((v, r), d) in enumerate(sorted(y_beats(j[0], 1).items()))] + [("F", 30)]
    assert check_trace(pt, j, [image(j[0]["W"], 1, 1)], ev) == []
    assert check_trace(pt, j, [image(j[0]["W"], 1, 1)], ev[:-2] + [("T", 40)])
    assert check_trace(pt, j, [image(j[0]["W"], 1, 1)], [("J", 5, 0), ("Q", 6, 1, 2)] + ev[2:])
    assert check_trace(pt, j, [image(j[0]["W"], 1, 1)], ev[:2] + [("D", 7)] + ev[3:])
    assert sum(stalls(3)) > 0 and sum(stalls(3, nominal=True)) == 0
    print("oracle self-test: ok")


if __name__ == "__main__":
    _selftest()
