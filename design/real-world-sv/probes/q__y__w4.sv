module t (input logic [7:0] a, output logic [3:0] y);
  always_comb begin
    y = '0;
    for (int unsigned i = 0; i < 8; i++) y += a[i];
  end
endmodule
