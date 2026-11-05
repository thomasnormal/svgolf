module q19_sub_chain_emax #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic [EW-1:0] ya, yb, em, e;
  logic adj;
  assign ya = {a[K-1:0], 1'b0};
  assign yb = {b[K-1:0], 1'b0};
  assign adj = a[0];
  assign em[W-2:0] = '1;
  assign em[EW-1:W-1] = '0;
  assign e = ya - yb + em - adj;
  assign q[EW-2:0] = e[EW-2:0];
endmodule
