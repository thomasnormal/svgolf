module t (input logic [7:0] a, output logic [7:0] y);
  logic [7:0] acc;
  always_comb begin
    acc = '0;
    for (int i = 0; i < 8; i++) acc[i] = a[7-i];
    y = acc;
  end
endmodule
