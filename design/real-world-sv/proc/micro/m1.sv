module m1 (input logic [7:0] a, b, output logic [14:0] p);
  always_comb begin
    p = '0;
    for (int i = 0; i < 8; i++) if (b[i]) p = p ^ (a << i);
  end
endmodule
