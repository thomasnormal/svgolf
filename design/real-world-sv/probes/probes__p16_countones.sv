module t (input logic [15:0] a, output logic [4:0] c);
  assign c = $countones(a);
endmodule
