// ATK-2: two always_ff drive q (a race). ls-sv resolves by sigma order; Yosys sees multiple drivers.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  always_ff @(posedge clk) if (rst) q <= '0; else if (en) q <= q + 1'b1;
  always_ff @(posedge clk) if (!rst && en) q <= q + 2'b10;
endmodule
