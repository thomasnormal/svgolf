module t #(parameter int N = 2) (input logic [N-1:0] a, output logic [N-1:0] y);
  assign y = a;
endmodule
module unrelated (input logic b, output logic z);
  assign z = undeclared_q;
endmodule
