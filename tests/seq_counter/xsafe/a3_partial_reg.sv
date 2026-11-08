// ATK-3: q[0] is the only bit ever assigned; q[N-1:1] is never written (holds power-up in ls-sv).
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  always_ff @(posedge clk) if (rst) q[0] <= 1'b0; else if (en) q[0] <= ~q[0];
endmodule
