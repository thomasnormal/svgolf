// CHECKER-LEGAL, TACTIC-READABLE (not an attack): a CORRECT ripple adder that names its top carry
// through a `localparam` (constant arithmetic is allowed, the banlist only bans run-time operators).
// This design used to be the advisory example of a tactic REFUSAL (`check.py --unproved --tactics`:
//   sv_structure: outside the supported fragment -- local parameters are outside the v1 fragment);
// since the localparam extension of the sv_comb tactics (PROVING.md, section 4) a `localparam int` /
// `localparam integer` defined by constant arithmetic over the parameters (+ - *, and / % by a
// literal) is one more named constant, so this one is INSIDE the fragment (in_fragment true). It is
// kept as the regression for that; localparam_clog2.sv and localparam_intdiv.sv are the refused shapes.
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  localparam int M = N - 1;
  logic [N:0] c;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign s[i]   = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
  endgenerate
  assign cout = c[M + 1];
endmodule
