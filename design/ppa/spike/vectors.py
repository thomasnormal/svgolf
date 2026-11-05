"""Pinned input vectors: vector k of a run is drawn from SHA-256("svgolf-ppa-spike/<seed>/<k>"),
uniform over all input bits, so the sequence is identical on every machine and Python version."""
import hashlib


def vector_bits(seed, k, nbits):
    h = hashlib.sha256(f"svgolf-ppa-spike/{seed}/{k}".encode()).digest()
    x = int.from_bytes(h, "big")
    assert nbits <= 256
    return [(x >> i) & 1 for i in range(nbits)]


def pi_values(pi_nets, nvec, seed):
    """{pi net: bitvector over vectors} for nvec vectors."""
    vals = {n: 0 for n in pi_nets}
    for k in range(nvec):
        bits = vector_bits(seed, k, len(pi_nets))
        for n, b in zip(pi_nets, bits):
            if b:
                vals[n] |= 1 << k
    return vals
