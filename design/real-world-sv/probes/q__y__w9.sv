module t (input logic [7:0] a, output logic [7:0] y);
  task automatic swap(input logic [7:0] x, output logic [7:0] z);
    z = {x[3:0], x[7:4]};
  endtask
  always_comb swap(a, y);
endmodule
