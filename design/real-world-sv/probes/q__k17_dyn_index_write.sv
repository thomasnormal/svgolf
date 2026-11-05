module t (input logic [2:0] s, input logic v, output logic [7:0] y);
  always_comb begin
    y = '0;
    y[s] = v;
  end
endmodule
