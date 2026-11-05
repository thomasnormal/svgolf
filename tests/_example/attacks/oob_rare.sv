// svGolf attack (_example): an out-of-range read confined to ONE input pair, the
// shape a score-gaining exploit would take. `rare` is 1 only at a = 16'hAAAA,
// b = 16'hB6DB (a reduction-AND detector, no comparison constant). There
// k[{rare, 2'b00}] reads k[4], past k's range: x. ls-sv and 4-state simulators
// (Icarus 12, measured 10/28): t is x, the
// if takes its else branch, y = a & b on every input, so the design is provably
// a & b. Yosys resolves the x to k[0] = 1, takes the then branch, and the
// netlist flips y[0] on that one input pair (measured: y = a28b where a & b =
// a28a). Random vectors hit it with probability 2^-32 and the harvest has no
// constant to aim with, so the post-synthesis check alone misses it: the
// fourstate stage refuses it exactly (a 3-bit run-time index into [3:0]).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [2*N-1:0] wa;
  logic [3*N-1:0] wb;
  logic [N-1:0]   pa, pb;
  logic           rare, t;
  logic [3:0]     k;
  assign wa   = {N{2'b10}};
  assign wb   = {N{3'b011}};
  assign pa   = wa[N-1:0];
  assign pb   = wb[N-1:0];
  assign rare = (&(~(a ^ pa))) & (&(~(b ^ pb)));
  assign k    = 4'b0001;
  assign t    = k[{rare, 2'b00}];
  always_comb
    if (t) y = (a & b) ^ {{(N-1){1'b0}}, rare};
    else y = a & b;
endmodule
