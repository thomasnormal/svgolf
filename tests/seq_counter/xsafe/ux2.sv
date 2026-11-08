// review4 probe: a never-reset self-holding register u decides two muxes whose results add to 1
// for either value of u. Correct from every power-up (rule 2).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u;
  always_ff @(posedge clk) begin
    u <= u;
    if (rst)     q <= '0;
    else if (en) q <= q + (u ? 1'b1 : 1'b0) + (u ? 1'b0 : 1'b1);
  end
endmodule
