module t (input logic [7:0] x, output logic [7:0] y);
  wire [7:0] rom [0:3];
  assign rom[0] = 8'h63;
  assign rom[1] = 8'h7c;
  assign rom[2] = 8'h77;
  assign rom[3] = 8'h7b;
  assign y = rom[x[1:0]];
endmodule
