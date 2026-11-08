// ATK-4: intermediate comb net w partially driven (w[0] only); w feeds the register q.
// MooreOutDep holds (q registered, no comb input->output path). w[N-1:1] undriven.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [N-1:0] w;
  assign w[0] = en;
  always_ff @(posedge clk) if (rst) q <= '0; else q <= w;
endmodule
