module q21_ternary_chain_fields #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic cn, ci, cz, ovf, fin;
  logic [K-2:0] mag;
  assign cn = a[0]; assign ci = a[1]; assign cz = a[2]; assign ovf = a[3];
  assign mag = b[K-2:0];
  assign fin = ~(cn | ci | cz | ovf);
  assign q[K-1] = ~cn & a[K-1];
  assign q[K-2:T] = (cn | ci | (~cz & ovf)) ? '1 : (cz ? '0 : mag[K-2:T]);
  assign q[T-1] = cn | (fin & mag[T-1]);
  genvar n;
  generate
    for (n = 0; n < T - 1; n = n + 1) begin : lo
      assign q[n] = fin & mag[n];
    end
  endgenerate
endmodule
