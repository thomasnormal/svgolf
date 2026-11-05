// H2 probe B7: overflow, normal range, subnormal shift amount (lines 113-120), as written.
module b7_shift (
  input  logic [6:0] eoff,
  output logic       ovf, nrm,
  output logic [6:0] dsh,
  output logic [3:0] sh
);
  assign ovf = (eoff >= 7'd63);
  assign nrm = (eoff >= 7'd33);
  assign dsh = 7'd33 - eoff;
  assign sh  = nrm ? 4'd0 : ((dsh >= 7'd12) ? 4'd12 : dsh[3:0]);
endmodule
