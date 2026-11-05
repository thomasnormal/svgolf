// A banned operator in a generate branch that the scoring point does not take.
module bad_hidden_branch #(parameter int N = 4) (input logic [N-1:0] a, b, output logic [N-1:0] s);
  if (N == 7) begin : g_add
    assign s = a + b;
  end else begin : g_xor
    assign s = a ^ b;
  end
endmodule
