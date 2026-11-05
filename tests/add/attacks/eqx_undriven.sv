// svGolf attack (add): `u === cin` with `u` undriven (x): never equal in IEEE
// 4-state simulation, so s/cout are the sum; Yosys reads the undriven net as a
// don't-care and the netlist drives 0 (0 GE). ls-sv has no `===` yet
// (UNSUPPORTED). Refused by the fourstate stage (Yosys `check`: `u` is used but
// has no driver); postsynth alone fails closed on it (ls-sv cannot evaluate it).
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
  logic u;
  assign s    = (u === cin) ? '0 : sr;
  assign cout = (u === cin) ? 1'b0 : cr;
endmodule
