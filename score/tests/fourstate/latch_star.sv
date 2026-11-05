// A variable an `always @*` block assigns on some paths only. Yosys's `proc` infers a latch for it WITHOUT the
// error it gives for always_comb: x in IEEE simulation until the first assignment (here: never, the condition is
// always false), 0 in the synthesized netlist. The rule is `select -assert-none t:$dlatch ...` after `proc`.
module latch_star #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  logic r;
  always @* begin
    if (a[0] & ~a[0]) r = 1'b1;
  end
  always @* begin
    if (!r) y = a | b;
    else y = a & b;
  end
endmodule
