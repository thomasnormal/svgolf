// micro: the field extracted by a concatenation of bit selects (no part select at all).
module m5_bits_cat (input logic [15:0] a, output logic [4:0] e);
  assign e = {a[14], a[13], a[12], a[11], a[10]};
endmodule
