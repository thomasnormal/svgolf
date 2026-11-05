module t (input logic [2:0] s, output logic [7:0] y);
  assign y = 8'b1 << s;
endmodule
