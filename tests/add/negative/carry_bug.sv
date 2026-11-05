// NEGATIVE (wrong gate): the carry cell drops b[i] from the propagate term,
// (a & b) | (c & a) instead of the majority (a & b) | (c & (a ^ b)).
// Refuted in Refute.lean by one run at N = 1: a = 0, b = 1, cin = 1 gives
// cout = 0, the task says 1.
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
    for (i = 0; i < N; i++) begin : g_bit
      assign s[i]   = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & a[i]);
    end
  endgenerate
  assign cout = c[N];
endmodule
