module t (input [7:0] a, b, output [15:0] p);
  function [15:0] clm;
    input [7:0] x, y;
    integer i;
    begin
      clm = 0;
      for (i = 0; i < 8; i = i + 1) if (y[i]) clm = clm ^ ({8'b0,x} << i);
    end
  endfunction
  assign p = clm(a, b);
endmodule
