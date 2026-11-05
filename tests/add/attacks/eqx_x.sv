// svGolf attack (add): `cin === 1'bx` selects 0. ls-sv has no `===` yet (an
// unsupported node: every run is UNSUPPORTED), so it is not provable today; a
// future ls-sv feature PR with IEEE semantics would make it so (cin is never x).
// Yosys folds `===` against x to a constant: the netlist drives 0 (0 GE).
// Refused by the source gate (an x/z literal digit); postsynth alone fails closed
// on it (ls-sv cannot evaluate it).
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N-1:0] sr;
  logic         cr;
  logic [N:0] c;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign sr[i]  = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
  endgenerate
  assign cr = c[N];
  assign s    = (cin === 1'bx) ? '0 : sr;
  assign cout = (cin === 1'bx) ? 1'b0 : cr;
endmodule
