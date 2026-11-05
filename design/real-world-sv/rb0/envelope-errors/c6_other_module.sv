module t (input logic a, output logic y);
  assign y = a;
endmodule
module unrelated (input logic b, output logic z);
  assign z = undeclared_q;
endmodule
