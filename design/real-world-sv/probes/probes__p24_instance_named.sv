module fa(input logic a, b, ci, output logic s, co);
  assign s = a ^ b ^ ci;
  assign co = (a & b) | (ci & (a ^ b));
endmodule
module t (input logic [3:0] a, b, output logic [3:0] s, output logic co);
  logic [4:0] c;
  assign c[0] = 1'b0;
  for (genvar i = 0; i < 4; i++) begin : g
    fa u (.a(a[i]), .b(b[i]), .ci(c[i]), .s(s[i]), .co(c[i+1]));
  end
  assign co = c[4];
endmodule
