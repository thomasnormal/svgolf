// H2 probe B8: subnormal shift, sticky and rounding (lines 122-132), as written (run-time shifts, concat operand of +).
module b8_round (
  input  logic [11:0] qm,
  input  logic        st0, nrm,
  input  logic [3:0]  sh,
  input  logic [6:0]  eoff,
  output logic [14:0] mag
);
  logic [11:0] qs;
  logic        st1, rb, inc;
  logic [4:0]  ef;
  assign qs  = qm >> sh;
  assign st1 = st0 | ((qs << sh) != qm);
  assign rb  = qs[0];
  assign inc = rb & (st1 | qs[1]);
  assign ef  = nrm ? eoff[4:0] : 5'd0;
  assign mag = {ef, qs[10:1]} + {14'd0, inc};
endmodule
