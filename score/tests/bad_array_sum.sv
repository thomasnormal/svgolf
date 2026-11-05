// An array reduction method on run-time data: `.sum()` adds the elements.
module bad_array_sum #(parameter int N = 4) (input logic [N-1:0] a, input logic [N-1:0] b,
                                             output logic [N-1:0] y);
  logic [N-1:0] arr [2];
  assign arr[0] = a & b;
  assign arr[1] = '0;
  assign y = arr.sum();
endmodule
