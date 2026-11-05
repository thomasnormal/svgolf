module t (input logic [4:0] a, output logic [4:0] y);
  for (genvar x = 0; x < 5; x++) begin : g
    assign y[x] = a[(x+1)%5] ^ a[(x+4)%5];
  end
endmodule
