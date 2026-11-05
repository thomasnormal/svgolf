// svGolf attack (_example): an out-of-range read confined to about 2^-9 of the inputs,
// the case between oob_select.sv (half the inputs) and oob_rare.sv (one pair). `rare` is
// 1 when the low 9 bits of a equal a fixed pattern (a reduction-AND detector, no comparison
// constant for the harvest to aim with; the pattern is none of the all-0, all-1 and
// walking vectors). There k[{rare, 2'b00}] reads k[4], past k's range: x. ls-sv and
// 4-state simulators: t is x, the if takes its else branch, y = a & b on every input, so the
// design is provably a & b. Yosys resolves the x to k[0] = 1, takes the then branch, and the
// netlist flips y[0] there. FULL post-synthesis mode (4000 random vectors) hits the region;
// LIGHT mode (about 190 random vectors) usually does not: the sampling boundary between
// the two modes, `postsynth_mode: full` in tests/expected.json. The fourstate stage refuses
// it exactly (a 3-bit run-time index into [3:0]).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [2*N-1:0] wa;
  logic [N-1:0]   pa, ma;
  logic           rare, t;
  logic [3:0]     k;
  assign wa   = {N{2'b10}};
  assign pa   = wa[N-1:0];
  assign ma   = ~({N{1'b1}} << 9);
  assign rare = &(~(a ^ pa) | ~ma);
  assign k    = 4'b0001;
  assign t    = k[{rare, 2'b00}];
  always_comb
    if (t) y = (a & b) ^ {{(N-1){1'b0}}, rare};
    else y = a & b;
endmodule
