module t (input [7:0] a, b, output reg [15:0] p);
  integer i;
  always @* begin
    p = 0;
    for (i = 0; i < 8; i = i + 1)
      if (b[i]) p = p ^ ({8'b0, a} << i);
  end
endmodule
