module t (input logic [7:0] a, output logic [2:0] y);
  logic z4, z2, z1;
  logic [3:0] a4;
  logic [1:0] a2;
  assign z4 = ~|a[7:4];
  assign a4 = z4 ? a[3:0] : a[7:4];
  assign z2 = ~|a4[3:2];
  assign a2 = z2 ? a4[1:0] : a4[3:2];
  assign z1 = ~a2[1];
  assign y = {z4, z2, z1};
endmodule
