module t (input logic [31:0] a, b, c, d, output logic [31:0] ra, rd);
  function automatic logic [31:0] rotl(input logic [31:0] x, input int n);
    return (x << n) | (x >> (32 - n));
  endfunction
  assign ra = a + b;
  assign rd = rotl(d ^ ra, 16);
endmodule
