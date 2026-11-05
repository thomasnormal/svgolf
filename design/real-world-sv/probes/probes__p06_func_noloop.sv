module t (input logic [31:0] a, b, c, d, output logic [31:0] y);
  function automatic logic [31:0] rotl(input logic [31:0] x, input int n);
    return (x << n) | (x >> (32 - n));
  endfunction
  assign y = rotl(a ^ b, 16) + c + d;
endmodule
