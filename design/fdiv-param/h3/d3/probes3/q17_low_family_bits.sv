module q17_low_family_bits #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic fin;
  logic [K-2:0] mag;
  assign fin = a[0];
  assign mag = a[K-2:0];
  assign q[K-1] = b[0];
  assign q[K-2:T] = mag[K-2:T];
  assign q[T-1] = fin | mag[T-1];
  genvar n;
  generate
    for (n = 0; n < T - 1; n = n + 1) begin : lo
      assign q[n] = fin & mag[n];
    end
  endgenerate
endmodule
