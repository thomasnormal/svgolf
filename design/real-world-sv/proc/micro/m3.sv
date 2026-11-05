module m3 (input [7:0] a, b, output reg [14:0] p);
  integer i;
  always @* begin
    p = 0;
    for (i = 0; i < 8; i = i + 1) if (b[i]) p = p ^ (a << i);
  end
endmodule
