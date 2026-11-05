module m11 (input logic [7:0] a, output logic [7:0] y);
  always_comb begin
    y = a;
    y ^= 8'h55;
    y += 1;
  end
endmodule
