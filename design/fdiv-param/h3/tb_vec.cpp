// Verilator testbench: vectors (a, b, want) from a file, any format with W + P <= 64.
#include <cstdio>
#include <cstdlib>
#include "Vfdiv.h"
int main(int argc, char** argv) {
  Vfdiv top;
  FILE* f = fopen(argv[1], "rb");
  uint64_t v[3], n = 0, bad = 0;
  while (fread(v, 8, 3, f) == 3) {
    top.a = v[0]; top.b = v[1]; top.eval(); n++;
    if ((uint64_t)top.q != v[2]) { bad++; if (bad <= 3) fprintf(stderr, "MISMATCH a=%llx b=%llx got=%llx want=%llx\n", (unsigned long long)v[0], (unsigned long long)v[1], (unsigned long long)top.q, (unsigned long long)v[2]); }
  }
  printf("{\"vectors\": %llu, \"mismatches\": %llu}\n", (unsigned long long)n, (unsigned long long)bad);
  return bad ? 1 : 0;
}
