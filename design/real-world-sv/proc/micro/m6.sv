module m6 (input logic [7:0] a, b, output logic [7:0] y);
  function automatic logic [7:0] f(input logic [7:0] x, k);
    logic [7:0] t;
    t = x ^ k;
    f = t & x;
  endfunction
  assign y = f(a, b);
endmodule
