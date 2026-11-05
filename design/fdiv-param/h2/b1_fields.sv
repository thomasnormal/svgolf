// H2 probe B1: fields, operand classes (reference lines 35-53), as written.
module b1_fields (
  input  logic [15:0] a,
  input  logic [15:0] b,
  output logic        s,
  output logic        a_nan, b_nan, a_inf, b_inf, a_zero, b_zero
);
  logic        sa, sb;
  logic [4:0]  ea, eb;
  logic [9:0]  fa, fb;
  assign sa = a[15];
  assign sb = b[15];
  assign s  = sa ^ sb;
  assign ea = a[14:10];
  assign eb = b[14:10];
  assign fa = a[9:0];
  assign fb = b[9:0];
  assign a_nan  = (ea == 5'd31) && (fa != 10'd0);
  assign b_nan  = (eb == 5'd31) && (fb != 10'd0);
  assign a_inf  = (ea == 5'd31) && (fa == 10'd0);
  assign b_inf  = (eb == 5'd31) && (fb == 10'd0);
  assign a_zero = (ea == 5'd0) && (fa == 10'd0);
  assign b_zero = (eb == 5'd0) && (fb == 10'd0);
endmodule
