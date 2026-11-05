// casez items may use z and ? as wildcards, casex items x, z and ?: both tools
// read them as "matches anything" (no other x/z digit is accepted).
module m(input logic [3:0] a, b, output logic [3:0] y);
  always_comb begin
    casez (a)
      4'b1??0, 4'b01z?: y = a | b;
      4'd?: y = b;
      default: y = a & b;
    endcase
    casex (b)
      {2'bx1, 2'b0z}: y = a;
      default: y = y;
    endcase
  end
endmodule
