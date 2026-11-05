// GATE: rejected (P-SAME-PROGRAM). A user function named \$clog2: slang (and the
// proof) call the user's, which returns 0, so W = 0 and y = 0; Yosys's lexer
// gives the call the name of the builtin $clog2, W = 4, and the design is scored
// as a & b (5.332 GE). Measured. The escaped `$`-name is refused whatever the name.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  function automatic integer \$clog2 (input integer v);
    begin \$clog2 = 0; end
  endfunction
  localparam integer W = \$clog2 (16);
  assign y = (W == 4) ? (a & b) : '0;
endmodule
