// D1: arithmetic right shift of a signed value (sign fill). defined-value; no x.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic signed [7:0] s;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; s <= 8'sb11110000; end
    else q <= s >>> 2;
endmodule
