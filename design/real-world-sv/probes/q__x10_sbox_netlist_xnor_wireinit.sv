module t (input logic [7:0] x, output logic [7:0] y);
  wire t1 = x[0] ^ x[3];
  wire t2 = x[1] ~^ x[2];
  wire m1 = t1 & t2;
  assign y = {m1, t1, t2, x[4], x[5] ^ x[6], 1'b1, x[7], ~x[0]};
endmodule
