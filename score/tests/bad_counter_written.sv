// A loop counter that the loop BODY writes is not a constant: `k + 1` reads
// the run-time value the body stored. (Yosys ignores the in-body write and
// folds the loop to `r = a ^ 2`, so only the front check sees this; the
// extractor refuses the loop.)
module bad_counter_written #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N:0]   r
);
  always_comb begin
    r = '0;
    for (int k = 0; k < 2; k++) begin
      k = int'(a[0]);
      r = {1'b0, a} ^ (k + 1);
    end
  end
endmodule
