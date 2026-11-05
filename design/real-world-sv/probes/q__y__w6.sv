module t (input logic [7:0] a, output logic [7:0] y);
  function automatic [7:0] f(input [7:0] x);
    f = x ^ 8'h1b;
  endfunction
  assign y = f(a);
endmodule
