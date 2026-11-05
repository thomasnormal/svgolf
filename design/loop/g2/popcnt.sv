// Population count over N bits (WS3 loop-shape sizing, design (b)): one-level arithmetic
// accumulator with a non-XOR step, the accumulator 32 bits wide.
module popcnt #(parameter int N = 8) (
  input  logic [N-1:0] a,
  output logic [31:0]  cnt
);
  always_comb begin
    cnt = '0;
    for (int i = 0; i < N; i++)
      cnt = cnt + a[i];
  end
endmodule
