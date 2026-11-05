// A localparam that is x without an x literal: a constant division by zero.
// As a case item it never matches in ls-sv; Yosys drops its x bits, so the
// item matches every input.
module param_divzero #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  localparam logic [3:0] K = 4'd1 / 4'd0;
  always_comb case (a[3:0]) K: y = a | b; default: y = a & b; endcase
endmodule
