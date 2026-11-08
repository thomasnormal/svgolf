// C2: run-time division by a possibly-zero divisor (en). ls-sv: x when en=0. fourstate catches only
// CONSTANT div-by-zero; the clocked banlist is empty; so only rule 3 (XSafe) should refuse this.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [N-1:0] d;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; d <= 8'd12; end
    else q <= d / {7'b0, en};
endmodule
