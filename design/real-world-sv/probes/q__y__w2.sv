module t (input logic [7:0] a, output logic [7:0] y);
  logic [7:0] arr [4];
  always_comb begin
    arr = '{default: '0};
    arr[1] = a;
    y = arr[1];
  end
endmodule
