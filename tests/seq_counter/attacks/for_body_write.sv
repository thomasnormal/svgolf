// expect: write to the `for` loop iterator `i` outside its header step
module cnt #(parameter int N = 8) (
  input  logic clk, rst, en,
  output logic [N-1:0] q
);
  always_ff @(posedge clk)
    if (rst)
      for (int i = 0; i < N; i++) begin
        q[i] <= 1'b0;
        i = i + 1;
      end
    else if (en)
      q <= q + 1'b1;
endmodule
