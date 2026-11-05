// svGolf attack (_example): the z/x bits hide in localparams built by
// concatenation. ls-sv: neither item ever matches, y = a & b. Yosys drops the
// x/z bits: K0 matches a[1] = 0 and K1 matches a[1] = 1, so the netlist is
// a | b. Refused by the source gate (the literal `1'bz` / `1'bx` digits).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  localparam logic [1:0] K0 = {1'b0, 1'bz};
  localparam logic [1:0] K1 = {1'b1, 1'bx};
  always_comb
    case (a[1:0])
      K0: y = a | b;
      K1: y = a | b;
      default: y = a & b;
    endcase
endmodule
