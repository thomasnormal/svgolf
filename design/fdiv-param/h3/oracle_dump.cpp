#include <cstdio>
#include <cstdlib>
#include "oracle.h"
int main(int argc, char** argv) {
  int W = atoi(argv[1]), P = atoi(argv[2]);
  uint64_t n = 1ULL << (W + P);
  FILE* f = fopen(argv[3], "wb");
  for (uint64_t a = 0; a < n; a++) for (uint64_t b = 0; b < n; b++) { uint64_t r = oracle_div(W, P, a, b); fwrite(&r, 4, 1, f); }
  fclose(f);
  return 0;
}
