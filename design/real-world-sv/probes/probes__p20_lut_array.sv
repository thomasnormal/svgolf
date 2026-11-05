module t (input logic [1:0] x, output logic [3:0] y);
  localparam logic [3:0] T [4] = '{4'h1, 4'h2, 4'h4, 4'h8};
  assign y = T[x];
endmodule
