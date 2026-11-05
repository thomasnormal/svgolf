// NEGATIVE (banlist): the behavioral product. Correct, but run-time `*` is
// banned in this task; rejected at the `banlist` stage (front check and the
// Yosys backstop's $mul cell).
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  assign p = a * b;
endmodule
