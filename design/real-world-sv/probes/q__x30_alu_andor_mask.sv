module t (input logic [1:0] sel, input logic [7:0] a, b, output logic [7:0] y);
  logic [7:0] s_add, s_and, s_xor;
  assign s_add = a + b;
  assign s_and = a & b;
  assign s_xor = a ^ b;
  assign y = ({8{sel == 2'd0}} & s_add) | ({8{sel == 2'd1}} & s_and) | ({8{sel == 2'd2}} & s_xor);
endmodule
