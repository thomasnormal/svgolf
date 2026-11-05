// A constant index past the range (here a write, w[8] of w[7:0], at the last
// generate iteration): refused like a read (slang's IndexOOB), conservatively.
module const_oob_write #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  logic [7:0] w;
  assign w[4:0] = '0;
  genvar i;
  for (i = 0; i < N; i++) begin : g
    assign w[i + 5] = a[i];
  end
  assign y = w[7:4] & b;
endmodule
