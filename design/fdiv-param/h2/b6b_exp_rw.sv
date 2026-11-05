// H2 probe B6b: the same sum with implicit zero extension (slang's Resize marker): the idiomatic way to write it.
module b6b_exp_rw (
  input  logic [4:0] xa, xb,
  input  logic [3:0] lza, lzb,
  input  logic       adj,
  output logic [6:0] eoff
);
  assign eoff = xa + lzb + 7'd47 - xb - lza - adj;
endmodule
