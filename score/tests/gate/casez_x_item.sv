// an `x` digit in a casez item is not a wildcard (only z and ? are): IEEE
// compares it as x, which never matches a known input.
module m(input logic [3:0] a, b, output logic [3:0] y);
  always_comb
    casez (a)
      4'b1x?0: y = a | b;
      default: y = a & b;
    endcase
endmodule
