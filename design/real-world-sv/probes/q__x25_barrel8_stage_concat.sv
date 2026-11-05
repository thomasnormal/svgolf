module t (input logic [7:0] a, input logic [2:0] s, output logic [7:0] y);
  logic [7:0] s1, s2;
  assign s1 = s[0] ? {a[6:0], 1'b0} : a;
  assign s2 = s[1] ? {s1[5:0], 2'b00} : s1;
  assign y  = s[2] ? {s2[3:0], 4'b0000} : s2;
endmodule
