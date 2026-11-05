// Exhaustive (or sampled) Verilator testbench for fdiv #(W, P) against oracle.h. Usage: vfdiv LO HI [SAMPLES SEED]
// exhaustive: a in [LO, HI), every b; sampled: SAMPLES random pairs (plus the corner patterns) and a in [LO, HI) ignored.
#include <cstdio>
#include <cstdlib>
#include <vector>
#include "Vfdiv.h"
#include "oracle.h"
#ifndef WW
#error define WW and PP
#endif
static uint64_t rng_s;
static inline uint64_t rnd() { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
int main(int argc, char** argv) {
  const int W = WW, P = PP, K = W + P;
  Vfdiv top;
  uint64_t mism = 0, pairs = 0, ex[3][3]; int nex = 0;
  auto check = [&](uint64_t a, uint64_t b) {
    top.a = a; top.b = b; top.eval();
    uint64_t want = oracle_div(W, P, a, b), got = top.q;
    pairs++;
    if (got != want) { mism++; if (nex < 3) { ex[nex][0] = a; ex[nex][1] = b; ex[nex][2] = got | (want << 32 & 0); nex++; fprintf(stderr, "MISMATCH a=%llx b=%llx got=%llx want=%llx\n", (unsigned long long)a, (unsigned long long)b, (unsigned long long)got, (unsigned long long)want); } }
  };
  const uint64_t n = (K >= 64) ? 0 : (1ULL << K);
  if (argc >= 4 && atoll(argv[3]) > 0) {
    uint64_t samples = atoll(argv[3]); rng_s = argc >= 5 ? atoll(argv[4]) * 2654435761ULL + 88172645463325252ULL : 88172645463325252ULL;
    const uint64_t mask = (K >= 64) ? ~0ULL : (n - 1);
    // corner patterns: every field extreme, signs 0/1
    std::vector<uint64_t> corners;
    const uint64_t mW = (1ULL << W) - 1, tm = (1ULL << (P - 1)) - 1;
    uint64_t es[] = {0, 1, 2, mW - 2, mW - 1, mW, (1ULL << (W - 1)) - 1, 1ULL << (W - 1), (1ULL << (W - 1)) - 2, (1ULL << (W - 1)) + 1};
    uint64_t fs[] = {0, 1, 2, tm, tm - 1, 1ULL << (P - 2), (1ULL << (P - 2)) - 1, (1ULL << (P - 2)) + 1, tm >> 1};
    for (uint64_t s : {0ULL, 1ULL}) for (uint64_t e : es) for (uint64_t f : fs)
      corners.push_back((s << (K - 1)) | ((e & mW) << (P - 1)) | (f & tm));
    for (uint64_t x : corners) for (uint64_t y : corners) check(x & mask, y & mask);
    for (uint64_t i = 0; i < samples; i++) check(rnd() & mask, rnd() & mask);
    // near-ties and near-overflow: random fractions with extreme exponents
    for (uint64_t i = 0; i < samples; i++) {
      uint64_t e1 = es[rnd() % 10], e2 = es[rnd() % 10];
      uint64_t a = ((rnd() & 1) << (K - 1)) | ((e1 & mW) << (P - 1)) | (rnd() & tm);
      uint64_t b = ((rnd() & 1) << (K - 1)) | ((e2 & mW) << (P - 1)) | (rnd() & tm);
      check(a & mask, b & mask);
    }
  } else {
    uint64_t lo = argc >= 3 ? atoll(argv[1]) : 0, hi = argc >= 3 ? atoll(argv[2]) : n;
    for (uint64_t a = lo; a < hi; a++) for (uint64_t b = 0; b < n; b++) check(a, b);
  }
  printf("{\"W\": %d, \"P\": %d, \"pairs\": %llu, \"mismatches\": %llu}\n", W, P, (unsigned long long)pairs, (unsigned long long)mism);
  return mism ? 1 : 0;
}
