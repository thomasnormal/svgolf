// `.xor()` is a bitwise reduction, not arithmetic: the front check passes it.
module ok_array_xor #(parameter int N = 4) (input logic [N-1:0] a, input logic [N-1:0] b,
                                            output logic [N-1:0] y);
  logic [N-1:0] arr [2];
  assign arr[0] = a;
  assign arr[1] = b;
  assign y = arr.xor();
endmodule
