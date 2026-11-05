module t (input logic [7:0] x, output logic [7:0] y);
  localparam logic [7:0] T [4] = '{8'h63, 8'h7c, 8'h77, 8'h7b};
  assign y = T[x[1:0]];
endmodule
