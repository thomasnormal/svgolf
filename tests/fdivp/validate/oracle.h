// Exact RNE division oracle for any binary format (W >= 2, P >= 2, W + P <= 64), 128-bit integers only.
// The quotient is rounded at the spacing of its binade; every shift is bounded (|s| <= 2P + 3), so no big integers.
#include <cstdint>
typedef unsigned __int128 u128;
static inline int bitlen(u128 x) { int n = 0; while (x) { n++; x >>= 1; } return n; }
static inline uint64_t oracle_div(int W, int P, uint64_t a, uint64_t b) {
  const int K = W + P, T = P - 1;
  const int64_t emax = (1LL << (W - 1)) - 1;
  const uint64_t mW = (1ULL << W) - 1;
  const uint64_t sa = (a >> (K - 1)) & 1, ea = (a >> T) & mW, fa = a & ((1ULL << T) - 1);
  const uint64_t sb = (b >> (K - 1)) & 1, eb = (b >> T) & mW, fb = b & ((1ULL << T) - 1);
  const uint64_t NAN_ = (mW << T) | (1ULL << (T - 1));
  const bool a_nan = ea == mW && fa != 0, b_nan = eb == mW && fb != 0;
  const bool a_inf = ea == mW && fa == 0, b_inf = eb == mW && fb == 0;
  const bool a_zero = ea == 0 && fa == 0, b_zero = eb == 0 && fb == 0;
  const uint64_t s = sa ^ sb;
  if (a_nan || b_nan || (a_inf && b_inf) || (a_zero && b_zero)) return NAN_;
  const uint64_t INF = (s << (K - 1)) | (mW << T), ZERO = s << (K - 1);
  if (a_inf || b_zero) return INF;
  if (b_inf || a_zero) return ZERO;
  const u128 siga = ea == 0 ? fa : ((u128)1 << T) + fa, sigb = eb == 0 ? fb : ((u128)1 << T) + fb;
  const int64_t qa = (ea > 1 ? (int64_t)ea : 1) - emax - T, qb = (eb > 1 ? (int64_t)eb : 1) - emax - T;
  const int64_t qmin = 1 - emax - T;
  const int64_t e = qa - qb - qmin;                       // the quotient in units: siga * 2^e / sigb
  int g = bitlen(siga) - bitlen(sigb);                    // floor(log2(siga / sigb))
  if (g >= 0) { if (siga < (sigb << g)) g--; } else { if ((siga << (-g)) < sigb) g--; }
  const int64_t l = g + e;                                // floor(log2) of the quotient in units
  const bool sub = l < T;
  const int64_t sh = sub ? e : (T - g);                   // M = round(siga * 2^sh / sigb)
  u128 M;
  if (sh < -(int64_t)(P + 3)) M = 0;
  else {
    u128 N = siga, D = sigb;
    if (sh >= 0) N <<= sh; else D <<= (-sh);
    M = N / D;
    const u128 rem = N % D;
    if (2 * rem > D || (2 * rem == D && (M & 1))) M += 1;
  }
  if (sub) {
    if (M >= ((u128)1 << T)) return (s << (K - 1)) | (1ULL << T) | (uint64_t)(M - ((u128)1 << T));   // M == 2^T: E = 1
    return (s << (K - 1)) | (uint64_t)M;
  }
  int64_t E = l - T + 1;
  if (M == ((u128)1 << P)) { M = (u128)1 << T; E += 1; }
  if (E >= (int64_t)mW) return INF;
  return (s << (K - 1)) | ((uint64_t)E << T) | (uint64_t)(M - ((u128)1 << T));
}
