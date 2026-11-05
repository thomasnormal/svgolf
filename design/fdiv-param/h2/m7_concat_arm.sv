// micro: a concatenation as an ARM of ?: (the mux shifter's `sh[0] ? {1'd0, qm[11:1]} : qm`).
module m7_concat_arm (input logic c, input logic [3:0] x, output logic [3:0] y);
  localparam integer W4 = 4;
  logic [W4-1:0] xw;
  assign xw = x;
  assign y = c ? {1'd0, xw[3:1]} : xw;
endmodule
