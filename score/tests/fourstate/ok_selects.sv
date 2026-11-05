// Run-time selects whose index cannot leave the range (a 3-bit index into
// [7:0], a 2-bit base of a 4-wide `+:` into [7:0]... [5:0]), genvar-indexed
// selects, constant arithmetic: nothing here can produce an x.
module ok_selects #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic [2:0]   i,
  output logic [N-1:0] y
);
  localparam logic [3:0] P = 4'b0101;
  logic [7:0] k;
  logic [N:0] c;
  assign k = {a, b};
  assign c[0] = 1'b0;
  genvar g;
  for (g = 0; g < N; g++) begin : gb
    assign c[g+1] = c[g] ^ a[g];
  end
  assign y = {k[i], k[i[1:0] +: 4] ^ P[3:1]} ^ c[N:1];
endmodule
