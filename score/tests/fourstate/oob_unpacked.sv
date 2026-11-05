// An unpacked array of 6 elements indexed by a 3-bit run-time value.
module oob_unpacked #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic [2:0]   i,
  output logic [N-1:0] y
);
  logic [N-1:0] arr [0:5];
  assign arr[0] = a; assign arr[1] = b; assign arr[2] = a & b;
  assign arr[3] = a | b; assign arr[4] = a ^ b; assign arr[5] = ~a;
  assign y = arr[i];
endmodule
