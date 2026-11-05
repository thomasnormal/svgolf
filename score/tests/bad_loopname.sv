// A module signal that shares its NAME with a procedural loop counter is still
// a run-time value: `y = i + j` is a run-time adder (front check by symbol
// identity, not by name).
module bad_loopname #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y,
  output logic [N-1:0] z
);
  logic [N-1:0] i, j;
  assign i = a;
  assign j = b;
  always_comb begin
    for (int i = 0; i < 1; i++) begin z[i+1] = a[i]; end
    for (int j = 0; j < 1; j++) begin end
    y = i + j;
  end
endmodule
