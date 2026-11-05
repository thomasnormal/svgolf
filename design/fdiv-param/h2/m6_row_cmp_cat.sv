// micro: comparison/difference with a concatenation operand, row of a literal-dim array.
module m6_row_cmp_cat (input logic [10:0] n, d, output logic g, output logic [11:0] t);
  logic [12:0] w;
  assign w = {1'b0, n, 1'b0};
  assign g = (w[11:0] >= {1'b0, d});
  assign t = w[11:0] - {1'b0, d};
endmodule
