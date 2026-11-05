// H2 style S5: a package with a packed struct and localparams for the format (fpnew / PULP style).
package fp_pkg;
  localparam int unsigned EXP_BITS = 5;
  localparam int unsigned MAN_BITS = 10;
  typedef struct packed {
    logic                s;
    logic [EXP_BITS-1:0] e;
    logic [MAN_BITS-1:0] m;
  } fp16_t;
endpackage

module s5_pkg_struct (
  input  fp_pkg::fp16_t a,
  output logic          is_nan
);
  import fp_pkg::*;
  assign is_nan = (a.e == '1) && (a.m != '0);
endmodule
