"""Cross-checks of oracle.py's quarter round against independent implementations (run with python3.12:
needs `cryptography`, whose ChaCha20 is OpenSSL's):
 1. the RFC 8439 Section 2.1.1 and 2.2.1 quarter-round vectors;
 2. the full ChaCha20 block function built on oracle.qr equals OpenSSL's keystream block 0 for random keys.
"""
import os, sys, random, struct
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oracle import qr, M

def vectors():
    assert qr(0x11111111, 0x01020304, 0x9b8d6f43, 0x01234567) == (0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb)
    assert qr(0x516461b1, 0x2a5f714c, 0x53372767, 0x3d631689) == (0xbdb886dc, 0xcfacafd2, 0xe46bea80, 0xccc07c79)
    return 2

def block(key, counter, nonce):
    s = list(struct.unpack("<4I", b"expand 32-byte k")) + list(struct.unpack("<8I", key)) + [counter] + list(struct.unpack("<3I", nonce))
    w = list(s)
    for _ in range(10):
        for (i, j, k, l) in ((0,4,8,12),(1,5,9,13),(2,6,10,14),(3,7,11,15),(0,5,10,15),(1,6,11,12),(2,7,8,13),(3,4,9,14)):
            w[i], w[j], w[k], w[l] = qr(w[i], w[j], w[k], w[l])
    return struct.pack("<16I", *[(w[i] + s[i]) & M for i in range(16)])

def openssl_check():
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms
    rnd = random.Random(4); n = 0
    for _ in range(50):
        key = bytes(rnd.getrandbits(8) for _ in range(32)); nonce = bytes(rnd.getrandbits(8) for _ in range(12)); ctr = rnd.getrandbits(32) & 0xFFFFF
        enc = Cipher(algorithms.ChaCha20(key, struct.pack("<I", ctr) + nonce), mode=None).encryptor()
        assert enc.update(bytes(64)) == block(key, ctr, nonce); n += 1
    return n

if __name__ == "__main__":
    print("RFC 8439 quarter-round vectors:", vectors())
    print("ChaCha20 blocks vs OpenSSL     :", openssl_check())
    print("ALL OK")
