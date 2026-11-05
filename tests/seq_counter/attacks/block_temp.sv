// expect: blocking assignment in `always_ff` to the block-local variable `t` (the clock-step profile, `Stmt2.nbaOnly`, does not admit block-local temporaries yet
module cnt #(parameter int N = 8) (
  input  logic clk, rst, en,
  output logic [N-1:0] q
);
  always_ff @(posedge clk) begin
    logic [N-1:0] t;
    t = q + 1'b1;
    if (rst)     q <= '0;
    else if (en) q <= t;
  end
endmodule
