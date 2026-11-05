module m5 (input logic [7:0] a, b, output logic [14:0] p);
  function automatic logic [14:0] clm(input logic [7:0] x, y);
    logic [14:0] r;
    r = '0;
    for (int i = 0; i < 8; i++) if (y[i]) r = r ^ (x << i);
    clm = r;
  endfunction
  assign p = clm(a, b);
endmodule
