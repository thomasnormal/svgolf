// H2 probe B8b: the shifter as a 4-stage mux barrel shifter that collects the sticky bit, the sum on a named concatenation.
module b8b_round_rw (
  input  logic [11:0] qm,
  input  logic        st0, nrm,
  input  logic [3:0]  sh,
  input  logic [6:0]  eoff,
  output logic [14:0] mag
);
  logic [11:0] q1, q2, q3, qs;
  logic        t1, t2, t3, st1, rb, inc;
  logic [4:0]  ef;
  logic [14:0] efq;
  assign q1  = sh[0] ? {1'd0, qm[11:1]} : qm;
  assign t1  = sh[0] & qm[0];
  assign q2  = sh[1] ? {2'd0, q1[11:2]} : q1;
  assign t2  = t1 | (sh[1] & (|q1[1:0]));
  assign q3  = sh[2] ? {4'd0, q2[11:4]} : q2;
  assign t3  = t2 | (sh[2] & (|q2[3:0]));
  assign qs  = sh[3] ? {8'd0, q3[11:8]} : q3;
  assign st1 = st0 | t3 | (sh[3] & (|q3[7:0]));
  assign rb  = qs[0];
  assign inc = rb & (st1 | qs[1]);
  assign ef  = nrm ? eoff[4:0] : 5'd0;
  assign efq = {ef, qs[10:1]};
  assign mag = efq + inc;
endmodule
