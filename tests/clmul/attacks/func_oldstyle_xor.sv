// STYLE: the shift-and-XOR as a function in the older Verilog-2001 form (`integer i`, result assigned to the
// function name, no `return`; fontamsoc/hw cpu/clmul.sv's `clmulFull`).
// Correct for every N. The scorer's Yosys frontend reads it (unlike the `return` form, func_shift_xor.sv); the
// loop counter is still a run-time index for the `fourstate` stage and a procedural loop for ls-sv.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  function automatic [2*N-2:0] clmul_full(input [N-1:0] x, input [N-1:0] y);
    integer i;
    reg [2*N-2:0] acc, xw;
    begin
      xw = {{(N-1){1'b0}}, x};
      acc = {(2*N-1){1'b0}};
      for (i = 0; i < N; i = i + 1)
        acc = acc ^ (y[i] ? (xw << i) : {(2*N-1){1'b0}});
      clmul_full = acc;
    end
  endfunction
  assign p = clmul_full(a, b);
endmodule
