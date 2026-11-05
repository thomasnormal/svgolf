module tie_probe(input logic [1:0] a, output logic [5:0] y);
  assign y = {a[0] & a[1], 1'b1, 1'b1, 1'b0, 1'b0, ~a[0]};
endmodule
