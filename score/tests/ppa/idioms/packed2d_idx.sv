// y = m[b[1:0]] over a packed 2-D array: the $shiftx leaves an escaped buffer with a 32'hxxxxxxxx constant that no gate reads.
// A PPA netlist-reader test design (score/tests/ppa/idioms.json): not a task submission, never banned or proved.
// check.py's postsynth stage refuses this netlist (an x literal in a dead buffer, fail closed), so only ppa.py and the leaderboard rescore read it.
module idiom #(parameter int N = 8) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [3:0][7:0] m;
  assign m = {a, b, a ^ b, a & b};
  assign y = m[b[1:0]];
endmodule
