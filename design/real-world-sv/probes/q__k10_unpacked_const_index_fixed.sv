module t (input logic [7:0] a, b, output logic [7:0] y);
  logic [7:0] arr [4];
  assign arr[0] = a;
  assign arr[1] = b;
  assign arr[2] = a ^ b;
  assign arr[3] = a & b;
  assign y = arr[2] | arr[3];
endmodule
