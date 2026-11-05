// The analysis error depends on the PARAMETER POINT: at N = 4 the two always_comb blocks write y[0]
// and y[1] (legal); at N = 2 both write y[0] (`multiple-always-assigns`). The verdict is per point, like
// every stage's.
module analysis_point #(parameter int N = 4) (
  input  logic [1:0] a,
  output logic [1:0] y
);
  always_comb y[0] = a[0];
  always_comb y[N/4] = a[1];
endmodule
