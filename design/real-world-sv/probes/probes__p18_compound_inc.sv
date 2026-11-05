module t (input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    y = a;
    y ^= b;
    y += 1;
  end
endmodule
