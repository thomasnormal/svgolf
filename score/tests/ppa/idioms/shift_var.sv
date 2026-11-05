// y = a >> b[2:0]: a variable shift. Dead public-named wires \_N_.A / \_N_.B / \_N_.Y are left by the techmapped $shr.
// A PPA netlist-reader test design (score/tests/ppa/idioms.json): not a task submission, never banned or proved.
module idiom #(parameter int N = 8) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  assign y = a >> b[2:0];
endmodule
