// Table fixture 12 (attack round 2, finding 2): a SIGNED dynamic read index. After reset i = 2'b11:
// ls-sv reads it unsigned (3) and m[3] = 1, so the counter counts; IEEE 1800 reads it signed (-1),
// out of [3:0], so m[i] is x and `if` takes the else branch.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] m;
  logic signed [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; m <= 4'b1000; i <= 2'b11; end
    else if (en && m[i]) q <= q + 1'b1;
endmodule
