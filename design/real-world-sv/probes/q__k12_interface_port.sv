interface bus_if;
  logic [7:0] d;
endinterface
module t #(parameter int N = 16) (bus_if b, input logic [7:0] a, output logic [7:0] y);
  assign y = a;
endmodule
