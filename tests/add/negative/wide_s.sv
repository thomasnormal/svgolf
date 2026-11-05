// NEGATIVE (interface, port width): the sum and the carry out share ONE
// (N+1)-bit output s = {cout, sum}, and there is no cout port. The bits are
// right, but the statement pins the outputs to exactly s (N bits) and cout
// (1 bit). Refuted in Refute.lean through the interface conjunct.
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N:0]   s
);
  logic [N:0] c;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign s[i]   = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
  endgenerate
  assign s[N] = c[N];
endmodule
