// SLANG ANALYSIS ERROR (mixed-var-assigns): continuous and procedural assignments to one variable (6.5)
// Decided 2026-11-01: "slang reports a program illegal" means the FULL slang driver, parse, elaboration AND
// analysis errors; `Compilation.getAllDiagnostics()` omits the analysis ones, so before the rule this design
// went through the banlist stage (and, for the shapes Yosys `check` does not see, through fourstate too).
// Otherwise the reference ripple adder (tasks/add/reference/add_n.sv).
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
  always_comb cout = c[N];
endmodule
