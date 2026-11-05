// svGolf attack (_example): a procedural for loop whose body writes its own counter
// (k = int'(a[0])). Yosys ignores the write and unrolls the loop (y = a & b, 21 GE);
// in an event-driven simulator the loop never ends when a[0] is 0 (Icarus 12 hung
// at time 0, measured 10/28).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    y = '0;
    for (int k = 0; k < 2; k++) begin
      k = int'(a[0]);
      y = y | (a & b);
    end
  end
endmodule
