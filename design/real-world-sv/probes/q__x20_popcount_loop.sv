module t (input logic [7:0] a, output logic [3:0] c);
  always_comb begin
    c = '0;
    for (int i = 0; i < 8; i++) c = c + a[i];
  end
endmodule
