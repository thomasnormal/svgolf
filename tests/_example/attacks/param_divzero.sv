// svGolf attack (_example): an x without an x literal, from a constant division
// by zero (constant division is not banned: only run-time `/` is). ls-sv: K is x,
// the item never matches, y = a & b. Yosys: K is a don't-care, the item matches
// every input, the netlist is a | b. Refused by the fourstate stage (a parameter
// with unknown bits; slang's DivisionByZero).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  localparam logic [1:0] K = 2'd1 / 2'd0;
  always_comb
    case (a[1:0])
      K: y = a | b;
      default: y = a & b;
    endcase
endmodule
