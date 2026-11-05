// svGolf task `add`, reference solution: an N-bit ripple-carry adder built
// from gates in one generate loop. c[i] is the carry INTO bit i; c[0] = cin,
// cout = c[N]. Per bit: the sum is a three-input XOR and the carry out is the
// majority of a[i], b[i], c[i], written as generate | (carry & propagate).
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
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
  endgenerate
  assign cout = c[N];
endmodule
