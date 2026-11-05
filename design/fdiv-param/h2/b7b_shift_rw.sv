// H2 probe B7b: the same with the comparisons named first (a comparison in a ?: condition is outside the fragment).
module b7b_shift_rw (
  input  logic [6:0] eoff,
  output logic       ovf, nrm,
  output logic [6:0] dsh,
  output logic [3:0] sh
);
  logic big;
  assign ovf = (eoff >= 7'd63);
  assign nrm = (eoff >= 7'd33);
  assign dsh = 7'd33 - eoff;
  assign big = (dsh >= 7'd12);
  assign sh  = nrm ? 4'd0 : (big ? 4'd12 : dsh[3:0]);
endmodule
