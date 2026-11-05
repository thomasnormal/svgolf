// svGolf attack (_example): a procedural for loop that skips an iteration by writing
// its counter (k = k + 1): in simulation y = a & b (the k == 1 iteration never runs);
// Yosys ignores the write, runs k == 1 and drives y = 0 (0 GE).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    y = a & b;
    for (int k = 0; k < 2; k++) begin
      if (k == 1) y = '0;
      k = k + 1;
    end
  end
endmodule
