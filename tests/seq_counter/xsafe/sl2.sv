// review4 probe: the index 2'sb11 >>> en is signed (the left operand's type, section 11.8.1) and
// -1 for every en; no signed signal, no cast.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic [3:0] m;
  always_ff @(posedge clk) begin
    if (rst)                             begin q <= '0; m <= 4'b1000; end
    else if (en && m[2'sb11 >>> en])     q <= q + 1'b1;
  end
endmodule
