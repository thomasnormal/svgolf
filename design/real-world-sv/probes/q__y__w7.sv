module t (input logic [7:0] a, output logic [7:0] y);
  logic [7:0] tmp;
  always_comb begin
    tmp = a;
    for (int i = 0; i < 8; i++) tmp = {tmp[6:0], tmp[7]};
    y = tmp;
  end
endmodule
