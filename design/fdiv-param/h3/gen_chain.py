#!/usr/bin/env python3
"""gen_chain.py N FLAVOR -> chain/cN_FLAVOR.sv and the Lean probe text.
FLAVOR whole: x_i = x_{i-1} ^ a (all [K-1:0] vectors); win: x_i written as two windows [T-1:0] and [K-1:T],
reading window [K-2:T] and [T-1:0] of the previous one (the unpack shape of the reference)."""
import sys
N = int(sys.argv[1]); fl = sys.argv[2]
name = f"c{N}_{fl}"
L = [f"module {name} #(parameter int W = 5, parameter int P = 11) (",
     "  input  logic [W+P-1:0] a, input logic [W+P-1:0] b, output logic [W+P-1:0] q);",
     "  localparam integer K = W + P;", "  localparam integer T = P - 1;"]
for i in range(N):
    L.append(f"  logic [K-1:0] x{i};")
if fl == "whole":
    L.append("  assign x0 = a ^ b;")
    for i in range(1, N):
        L.append(f"  assign x{i} = x{i-1} {'&' if i % 2 else '^'} a;")
else:
    L.append("  assign x0[T-1:0] = a[T-1:0] ^ b[T-1:0];")
    L.append("  assign x0[K-1:T] = a[K-1:T] ^ b[K-1:T];")
    for i in range(1, N):
        L.append(f"  assign x{i}[T-1:0] = x{i-1}[T-1:0] ^ a[T-1:0];")
        L.append(f"  assign x{i}[K-1:T] = x{i-1}[K-1:T] & a[K-1:T];")
L.append(f"  assign q = x{N-1};")
L.append("endmodule")
open(f"chain/{name}.sv", "w").write("\n".join(L) + "\n")
nsites = N + 1 if fl == "whole" else 2 * N + 1
print(name, nsites)
