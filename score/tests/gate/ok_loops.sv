// The procedural `for` headers score/srcgate.py item 7 admits, in `always_comb`, `always_ff` and a
// function: an `int`/`integer` iterator declared in the header, a condition `i <op> E` or
// `E <op> i`, E from unsized decimal literals, the iterator and `int`/`integer`/untyped-decimal
// parameters by + - *, one step on the iterator.
module band #(parameter int N = 4, parameter W = 8, parameter integer G = 2) (
  input  logic       clk,
  input  logic [7:0] a,
  output logic [7:0] y, z, v
);
  localparam L = 3;
  function automatic logic [7:0] rev(input logic [7:0] x);
    for (int b = 0; b < 8; b++) rev[b] = x[7 - b];
  endfunction
  always_comb begin
    y = '0;
    for (int i = 0; i < N; i++) y[i] = a[i];
    for (integer i = W - 1; i >= W - G; i--) y[i] = a[i];
    for (int signed i = 4; L + 2 > i; i += 1) y[i] = ~a[i];
    for (var int i = 7; i != 6; i = i - 1) y[i] = a[i] ^ a[0];
  end
  always_ff @(posedge clk)
    for (int i = (N - 1) * 2 - 6; i <= -1 + 2 * L - 4; i = i + 2) z[i] <= a[i];
  assign v = rev(a);
endmodule
