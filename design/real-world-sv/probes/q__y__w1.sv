module t (input logic [7:0] a, output logic [7:0] y);
  always_comb begin
    automatic logic [7:0] tmp = a ^ 8'h55;
    y = tmp;
  end
endmodule
