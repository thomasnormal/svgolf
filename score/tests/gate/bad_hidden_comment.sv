// GATE: rejected. Comment openers inside an escaped identifier and a string
// (Yosys's lexer might disagree with slang there), a pragma block comment,
// and a default_nettype other than none/wire.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a, input logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [N-1:0] \a//b ;
  initial $display("x // y");
  assign \a//b = a;
  /* synthesis translate_off */
  assign y = a & b;
  /*synopsys translate_on*/
endmodule
`default_nettype tri
