module t (input logic [31:0] a, input int n, output logic [31:0] y);
  assign y = (32'(a) << n);
endmodule
