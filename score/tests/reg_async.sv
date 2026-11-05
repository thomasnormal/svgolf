// An asynchronous reset: outside contract C1 (synchronous reset only); the clocked flow's
// `dfflegalize -cell $_DFF_P_ x` cannot legalize it, so the design is not scored.
module reg_async (input logic clk, input logic rst_n, input logic d, output logic q);
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) q <= 1'b0;
    else        q <= d;
endmodule
