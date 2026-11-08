// review4 probe: a dynamic index that IEEE 1800 types as SIGNED (both ?: arms are signed
// literals, section 11.8.1) although it mentions no signed signal and has no cast. With en = 1 the
// index is 2'sb11 = -1: out of range, the read is x and the if takes no count (IEEE), while ls-sv
// reads the index unsigned (3) and counts.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic [3:0] m;
  always_ff @(posedge clk) begin
    if (rst)                                begin q <= '0; m <= 4'b1000; end
    else if (en && m[en ? 2'b11 : 2'b01]) q <= q + 1'b1;
  end
endmodule
