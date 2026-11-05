module m7 (input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    logic [7:0] t1;
    t1 = a ^ b;
    y = t1 & a;
  end
endmodule
