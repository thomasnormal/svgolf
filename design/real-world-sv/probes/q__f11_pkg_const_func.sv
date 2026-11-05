package pk;
  localparam int W = 8;
  function automatic logic [7:0] f(input logic [7:0] x);
    return x ^ 8'h1b;
  endfunction
endpackage
module t #(parameter int N = 16) (input logic [7:0] a, output logic [7:0] y);
  import pk::*;
  assign y = f(a);
endmodule
