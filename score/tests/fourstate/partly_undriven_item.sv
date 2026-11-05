// A case item with an undriven bit: u = {a[1], x} never matches in ls-sv.
module partly_undriven_item #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  logic [1:0] u;
  assign u[1] = a[1];
  always_comb case (a[1:0]) u: y = a | b; default: y = a & b; endcase
endmodule
