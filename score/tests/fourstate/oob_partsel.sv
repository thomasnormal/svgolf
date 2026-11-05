// Indexed part selects whose run-time base can run past the range.
module oob_partsel #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic [2:0]   i,
  input  logic [1:0]   j,
  output logic [N-1:0] y
);
  logic [7:0] k;
  assign k = {a, b};
  assign y = k[i +: 4] ^ k[j -: 4];
endmodule
