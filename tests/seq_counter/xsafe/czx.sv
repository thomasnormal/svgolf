// review4 probe: an x digit in a casez item (not a wildcard in casez).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  always_ff @(posedge clk) begin
    if (rst) q <= '0;
    else casez (en)
      1'bx:    q <= '0;
      default: q <= q + 1'b1;
    endcase
  end
endmodule
