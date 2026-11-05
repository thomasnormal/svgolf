// Inline constant expressions that are x: a division by zero, 0 ** -1, and a
// constant function that returns a local it never assigns.
module const_inline_x #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  function automatic logic [3:0] f(input int k);
    logic [3:0] r;
    if (k > 100) r = 4'd1;
    f = r;
  endfunction
  always_comb begin
    y = a & b;
    if (a[0] == (4'd3 / 4'd0)) y = a | b;
    if (b[0] == (4'd0 ** -1)) y = a ^ b;
    if (a[1] == f(2)) y = b;
  end
endmodule
