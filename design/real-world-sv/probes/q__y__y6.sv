module t (input logic [31:0] a, output logic [31:0] y);
  assign y = {<<{a}};
endmodule
