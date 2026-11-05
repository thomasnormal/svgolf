module m3b (input logic [7:0] a, b, output logic [14:0] p);
  integer i;
  always_comb begin
    p = '0;
    for (i = 0; i < 8; i = i + 1) if (b[i]) p = p ^ (a << i);
  end
endmodule
