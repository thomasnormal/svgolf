// ADVISORY CHECK, not an attack on ls-sv/Yosys: a ripple adder whose carry cell drops the
// propagate term, (a & b) | (c & a) instead of the majority (a & b) | (c & (a ^ b)).
// ls-sv and the scored netlist read this text the same way, so EVERY stage before the proof
// passes it (`check.py --unproved` stops at `unproved` and scores it); only the Lean proof (or
// the advisory functional smoke check, `warnings` in the result) tells it from an adder.
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
