// GATE: passes. Comments of every shape (stripped), escaped identifiers,
// @(*), and the two admitted directives.
`timescale 1ns/1ps
`default_nettype none
// A carry chain; this comment mentions "quotes" and a // nested opener.
/* block comment
   spanning lines, with a "string" and // inside */
module band #(parameter int N = 4) ( // trailing comment
  input  logic [N-1:0] a, /* inline */ input logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [N-1:0] \t$x ;
  always @(*) begin \t$x = a & b; end
  always @( * ) y = \t$x ; // the synthesis-friendly form
endmodule
`default_nettype wire
