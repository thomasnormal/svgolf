module t (input logic [7:0] a, output logic [7:0] y);
  always_comb begin
    y = '0;
    foreach (a[i]) y[i] = a[i];
  end
endmodule
