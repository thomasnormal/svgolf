module t (input logic [31:0] d, output logic [5:0] p);
  assign p[0] = ^(d & 32'h2606BD25);
  assign p[1] = ^(d & 32'hDEBA8050);
  assign p[2] = ^(d & 32'h413D89AA);
  assign p[3] = ^(d & 32'h31234ED1);
  assign p[4] = ^(d & 32'hC2C092FD);
  assign p[5] = ^(d & 32'hF4A5B3D8);
endmodule
