// An initialized flip-flop (a free reset): outside contract C1; `dfflegalize ... x` (no
// initial value allowed) makes it a Yosys error, so the design is not scored.
module reg_init (input logic clk, input logic d, output logic q = 1'b1);
  always_ff @(posedge clk) q <= d;
endmodule
