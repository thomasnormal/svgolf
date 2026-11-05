package pk;
  function automatic logic [7:0] f(input logic [7:0] x);
    f = x ^ 8'h1b;
  endfunction
endpackage
module t (input logic [7:0] a, output logic [7:0] y);
  assign y = pk::f(a);
endmodule
