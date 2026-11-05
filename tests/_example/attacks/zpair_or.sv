// svGolf attack (_example): two complementary case items with a z bit. ls-sv and
// 4-state simulators (Icarus 12, measured 10/28) compare case items by ===:
// {a[0], b[0]} is never z, so no item matches
// and the default arm runs, y = a & b. Yosys drops the z bits from the comparison,
// so `2'b0z` matches a[0] = 0 and `2'b1z` matches a[0] = 1: together EVERY input,
// and the netlist is a | b. Refused by the source gate (an x/z literal digit).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb
    case ({a[0], b[0]})
      2'b0z: y = a | b;
      2'b1z: y = a | b;
      default: y = a & b;
    endcase
endmodule
