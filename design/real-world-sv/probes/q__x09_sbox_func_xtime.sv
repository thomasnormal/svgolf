module t (input logic [7:0] x, output logic [7:0] y);
  function automatic logic [7:0] xtime(input logic [7:0] b);
    xtime = {b[6:0], 1'b0} ^ (8'h1b & {8{b[7]}});
  endfunction
  assign y = xtime(x) ^ x;
endmodule
