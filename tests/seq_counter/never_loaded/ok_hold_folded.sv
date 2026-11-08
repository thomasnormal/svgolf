// expect: unproved
// warn: register `u` is never loaded
// A never-loaded register whose every read folds away (the acceptance table's fixture 0: q + (1 ^ (u ^ u))):
// Yosys folds u ^ u to 0 and removes the unread flop, so the netlist is the design's and the score stage
// accepts it; the source-level twin only warns.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u;
  always_ff @(posedge clk) begin
    u <= u;
    if (rst)     q <= '0;
    else if (en) q <= q + (1'b1 ^ (u ^ u));
  end
endmodule
