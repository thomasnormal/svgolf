// A correct ripple adder written STRUCTURALLY (one `full_adder` instance per bit, instantiated by a
// generate loop). The design and score stages accept it (the scorer flattens: it scores like
// `add_n`); the `sv_comb` tactics refuse module instances and say so (WP-I, step I0): the
// `--tactics` advisory answers "this design instantiates modules ...". Not an attack on the checker.
module full_adder (
  input  logic a, b, cin,
  output logic s, cout
);
  assign s    = a ^ b ^ cin;
  assign cout = (a & b) | (cin & (a ^ b));
endmodule

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
      full_adder fa (.a(a[i]), .b(b[i]), .cin(c[i]), .s(s[i]), .cout(c[i+1]));
    end
  endgenerate
  assign cout = c[N];
endmodule
