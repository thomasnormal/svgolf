// x/z literal digits: a case item and an `==` operand whose z bits Yosys drops
// (the complementary items match every input in Yosys, none in ls-sv), a
// localparam built from x/z literals, an unbased `'x` don't-care, a `?` digit.
module m(input logic [3:0] a, b, output logic [3:0] y);
  localparam logic [1:0] K = {1'b0, 1'bz};
  logic t;
  assign t = (a[1:0] == 2'b1z) ? 1'b1 : 1'b0;
  always_comb begin
    y = 'x;
    case ({a[0], b[0]})
      2'b0z: y = a | b;
      2'b1z: y = a | b;
      K: y = 4'd?;
      default: y = a & b;
    endcase
  end
endmodule
