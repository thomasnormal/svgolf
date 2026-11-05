// `initial` plus `always_comb` writers of one variable: slang's ANALYSIS pass reports
// `multiple-always-assigns` (an initial block is another process, IEEE 1800-2023 9.2.2.2); Xcelium
// `*E,MULAXX`. Yosys accepts the netlist, so before 2026-11-01 only the Lean loader (no `Initial`
// process kind) stood between this design and a score.
module analysis_initial_comb #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  initial y = '0;
  always_comb y = a;
endmodule
