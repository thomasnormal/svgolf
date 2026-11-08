// A run-time division in a task that bans no operator of its own: banned all the same (every task bans run-time
// / % **, banlist.py ALWAYS_BANNED). `b` can be 0, and then `a / b` is x in IEEE 1800 (ls-sv computes with it) while
// Yosys's divider gives a defined value.
module bad_div_any_task #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] q
);
  assign q = a / b;
endmodule
