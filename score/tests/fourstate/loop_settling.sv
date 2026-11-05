// A combinational loop that SETTLES for every input (mux feedback: y holds its value while s = 0). The pinned
// scoring flow prices it (one $_MUX_, 2.333 GE) and ls-sv's run2 completes it, so only this stage refuses loops
// (docs/sv-tools-split-audit.md, probe loop_mux; design/nondeterminism/NOTE.md section 7).
module loop_settling #(parameter int N = 4) (
  input  logic s,
  input  logic d,
  output logic y
);
  assign y = s ? d : y;
endmodule
