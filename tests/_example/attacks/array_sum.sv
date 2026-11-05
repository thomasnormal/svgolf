// svGolf attack (_example): an array reduction method, `arr.sum()`: run-time
// addition behind a method call (Yosys 0.53 cannot read it; slang can, on an
// unpacked array). The banlist's front check flags it under a + ban.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [N-1:0] arr [2];
  assign arr[0] = a & b;
  assign arr[1] = '0;
  assign y = arr.sum();
endmodule
