// svGolf attack (_example): an out-of-range read. k[{1'b1, a[1:0]}] is always past
// k's four bits, so it is x: ls-sv's t is x and the if takes its else branch,
// y = a & b. Yosys resolves the x to t = 1: the netlist is a | b. Refused by the
// fourstate stage (a run-time index that can leave the declared range).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [3:0] k;
  logic       t;
  assign k = 4'b0101;
  assign t = k[{1'b1, a[1:0]}] ? 1'b0 : 1'b1;
  always_comb
    if (t) y = a | b;
    else y = a & b;
endmodule
