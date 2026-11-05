module t (input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    y = '0;
    for (int i = 0; i < 8; i++) begin
      if (a[i]) break;
      y[i] = b[i];
    end
  end
endmodule
