module m13 (input logic [7:0] a, b, output logic [7:0] y);
  function automatic logic [7:0] f(input logic [7:0] x, k);
    return x ^ k;
  endfunction
  always_comb begin
    y = f(a, b) & a;
  end
endmodule
