module t (input logic [7:0] a, output logic [3:0] y);
  always_comb begin
    if (a[7]) y = 4'd0;
    else if (a[6]) y = 4'd1;
    else if (a[5]) y = 4'd2;
    else if (a[4]) y = 4'd3;
    else if (a[3]) y = 4'd4;
    else if (a[2]) y = 4'd5;
    else if (a[1]) y = 4'd6;
    else if (a[0]) y = 4'd7;
    else y = 4'd8;
  end
endmodule
