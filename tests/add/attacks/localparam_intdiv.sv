// CHECKER-LEGAL, TACTIC-REFUSED (not an attack): a CORRECT ripple adder with a 2-STATE `int`
// localparam defined by a division. `check.py --unproved --tactics` reports
//   sv_structure: outside the supported fragment -- localparam `H`: a 2-state `int` localparam
//   initialised by `/` or `%` is squashed to 2 states and wraps at 2^31 in the elaborated design ...
// (PROVING.md, section 4). The extractor wraps a `/` or `%` under an `int` target in a 2-state squash
// (the division may be x), which ls-sv reads as a wrap modulo 2^32: the closed form `(N + 1) / 2`
// would be false for the huge N a for-all-N theorem quantifies over. Declare it `localparam integer`
// (the 4-state twin, no squash) and the tactics accept it.
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  localparam int H = (N + 1) / 2;
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
