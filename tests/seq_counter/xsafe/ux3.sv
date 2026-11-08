// review4 probe: as ux2 with if/else decisions on the unreset self-holding u in two processes.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u, a, b;
  always_ff @(posedge clk) u <= u;
  always_comb begin
    if (u) a = 1'b1; else a = 1'b0;
    if (u) b = 1'b0; else b = 1'b1;
  end
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en && (a ^ b)) q <= q + 1'b1;
  end
endmodule
