// `$countones` of a run-time value: Yosys builds it from `$add` cells.
module bad_countones #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [7:0]   y
);
  assign y = $countones(a);
endmodule
