// NEGATIVE (banlist): Yosys's own adder, {cout, s} = a + b + cin. It computes
// the task's function (validate/validate.py checks it in Verilator and ls-sv),
// but run-time + is banned: score/banlist.py rejects it before Lean. Scored
// with the banlist lifted, it is the baseline to beat (README.md).
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  assign {cout, s} = a + b + cin;
endmodule
