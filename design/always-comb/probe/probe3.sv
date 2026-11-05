`timescale 1ns/1ns
// carry chain through always_comb blocks over bits of ONE vector c (the add_proc shape): block i reads c[i], writes c[i+1].
module chain3 (input logic [2:0] a, input logic [2:0] b, input logic cin, output logic [3:0] c, output logic [2:0] s);
  logic [2:0] p;
  assign c[0] = cin;
  assign p = a ^ b;
  always_comb begin if (p[0]) c[1] = c[0]; else c[1] = a[0]; end
  always_comb begin if (p[1]) c[2] = c[1]; else c[2] = a[1]; end
  always_comb begin if (p[2]) c[3] = c[2]; else c[3] = a[2]; end
  assign s = p ^ c[2:0];
endmodule
// the same chain with the two statements of one cell in ONE block (multi-target body)
module chain3m (input logic [2:0] a, input logic [2:0] b, input logic cin, output logic [3:0] c, output logic [2:0] s);
  logic [2:0] p;
  assign c[0] = cin;
  assign p = a ^ b;
  always_comb begin if (p[0]) c[1] = c[0]; else c[1] = a[0]; s[0] = p[0] ^ c[0]; end
  always_comb begin if (p[1]) c[2] = c[1]; else c[2] = a[1]; s[1] = p[1] ^ c[1]; end
  always_comb begin if (p[2]) c[3] = c[2]; else c[3] = a[2]; s[2] = p[2] ^ c[2]; end
endmodule
module tb;
  reg [2:0] a, b; reg cin;
  wire [3:0] c, cm; wire [2:0] s, sm;
  chain3 u (.a(a), .b(b), .cin(cin), .c(c), .s(s));
  chain3m um (.a(a), .b(b), .cin(cin), .c(cm), .s(sm));
  integer k;
  reg [8:0] v;
  initial begin
    // exhaustive + x/z cases; change only cin between consecutive steps to exercise the chain wake-ups
    for (k = 0; k < 64; k = k + 1) begin
      a = k[2:0]; b = k[5:3]; cin = 1'b0; #1; $display("CYCLE %0d a=%b b=%b cin=%b c=%b s=%b cm=%b sm=%b", 2*k, a, b, cin, c, s, cm, sm);
      cin = 1'b1; #1; $display("CYCLE %0d a=%b b=%b cin=%b c=%b s=%b cm=%b sm=%b", 2*k+1, a, b, cin, c, s, cm, sm);
    end
    a = 3'b0x1; b = 3'b110; cin = 1'b1; #1; $display("CYCLE 128 a=%b b=%b cin=%b c=%b s=%b cm=%b sm=%b", a, b, cin, c, s, cm, sm);
    a = 3'b101; b = 3'bx10; cin = 1'bz; #1; $display("CYCLE 129 a=%b b=%b cin=%b c=%b s=%b cm=%b sm=%b", a, b, cin, c, s, cm, sm);
    $finish;
  end
endmodule
