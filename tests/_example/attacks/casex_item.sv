// svGolf attack (_example): a case item `1'bx` on a signal that is 0. ls-sv and
// 4-state simulators (Icarus 12, measured 10/28) compare case items by ===, so the
// default arm runs: y = a & b. Yosys reads
// the x item as matching (a don't-care) and drives y with x: 0 GE. Refused by the
// source gate (an x/z literal digit outside a casez/casex wildcard); before that
// rule it passed every stage up to postsynth, which rejects it on every vector.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic s;
  assign s = 1'b0;
  always_comb
    case (s)
      1'bx: y = '0;
      default: y = a & b;
    endcase
endmodule
