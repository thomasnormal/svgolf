// y = 8'd1 << b[2:0]: a one-hot decode (a left shift of a constant).
// A PPA netlist-reader test design (score/tests/ppa/idioms.json): not a task submission, never banned or proved.
module idiom #(parameter int N = 8) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  assign y = 8'd1 << b[2:0];
endmodule
