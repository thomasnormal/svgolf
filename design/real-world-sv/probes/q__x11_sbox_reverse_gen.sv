module t (input logic [7:0] x, output logic [7:0] y);
  logic [7:0] u, s;
  for (genvar i = 0; i < 8; i++) begin : g
    assign u[i] = x[7-i];
    assign y[i] = s[7-i];
  end
  assign s = u ^ {u[6:0], 1'b0};
endmodule
