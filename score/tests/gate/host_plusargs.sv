// GATE: rejected (P-NO-HOST-ACCESS). Reads the command line of the host process.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  integer v;
  initial begin
    if ($test$plusargs("SALT")) $display("salt");
    if ($value$plusargs("SEED=%d", v)) $display("%d", v);
  end
  assign y = a & b;
endmodule
