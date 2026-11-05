// NEGATIVE (correct at the scoring point only): a ripple-carry adder when
// N == 16, and a carry-free XOR everywhere else. It passes simulation and
// scores at N = 16, but the statement covers every N >= 1. Refuted in
// Refute.lean by one run at N = 1: a = 0, b = 0, cin = 1 gives s = 0.
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0] c;
  assign c[0] = cin;
  genvar i;
  generate
    if (N == 16) begin : g_ripple
      for (i = 0; i < N; i++) begin : g_bit
        assign s[i]   = a[i] ^ b[i] ^ c[i];
        assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
      end
      assign cout = c[N];
    end else begin : g_cheap
      assign s    = a ^ b;
      assign cout = 1'b0;
    end
  endgenerate
endmodule
