// `$countones` of a constant: folded at elaboration, no cell.
module ok_countones_const #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  localparam int K = $countones(N);
  assign y = a << K;
endmodule
