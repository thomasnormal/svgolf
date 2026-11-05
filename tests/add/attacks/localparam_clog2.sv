// CHECKER-LEGAL, TACTIC-REFUSED (not an attack): a CORRECT ripple adder that carries a `localparam`
// defined by `$clog2` (the shape of the Sklansky and Kogge-Stone baselines' level count; constant
// arithmetic is allowed, the banlist only bans run-time operators). `check.py --unproved --tactics`
// reports
//   sv_structure: outside the supported fragment -- localparam `L`: `$clog2` is outside the v1 fragment ...
// (PROVING.md, section 4): a localparam may be an integer constant expression of the parameters built
// from + - * and / % by a literal; `$clog2` is not a linear function of N, and `paramEnv2` cannot even
// evaluate it at a symbolic N. The localparam is unused here, and refused all the same.
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  localparam int L = $clog2(N + 1);
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
