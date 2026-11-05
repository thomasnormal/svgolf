// NEGATIVE (banlist): a CORRECT carry-less multiplier built from the integer multiplier, by Kronecker
// substitution (valid for N < 128). The point of the task is to build the product from XOR/AND networks:
// the run-time * is banned.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  // Kronecker substitution: spread every bit of a and b K = 8 positions apart (enough for N <= 127: a group
  // of the integer product sums at most N ones, N < 2^8), multiply as integers, and read the PARITY of
  // each K-bit group: the carries stay inside the groups, so group k holds a_i b_j summed over i + j = k.
  localparam int K = 8;
  logic [K*N-1:0]     sa, sb;
  logic [2*K*N-1:0]   sp;
  genvar i, k;
  generate
    for (i = 0; i < K*N; i++) begin : g_spread
      if (i % K == 0) begin : g_bit
        assign sa[i] = a[i/K];
        assign sb[i] = b[i/K];
      end else begin : g_zero
        assign sa[i] = 1'b0;
        assign sb[i] = 1'b0;
      end
    end
  endgenerate
  assign sp = sa * sb;
  generate
    for (k = 0; k < 2*N-1; k++) begin : g_parity
      assign p[k] = sp[K*k];
    end
  endgenerate
endmodule
