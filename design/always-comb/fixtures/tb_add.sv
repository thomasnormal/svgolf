`timescale 1ns/1ns
module tb;
  localparam N4 = 4, N16 = 16;
  reg [N4-1:0] a4, b4; reg c4;
  wire [N4-1:0] s4, s4m; wire co4, co4m;
  add_proc #(.N(N4)) u4 (.a(a4), .b(b4), .cin(c4), .s(s4), .cout(co4));
  add_proc_m #(.N(N4)) u4m (.a(a4), .b(b4), .cin(c4), .s(s4m), .cout(co4m));
  reg [N16-1:0] a16, b16; reg c16;
  wire [N16-1:0] s16, s16m; wire co16, co16m;
  add_proc #(.N(N16)) u16 (.a(a16), .b(b16), .cin(c16), .s(s16), .cout(co16));
  add_proc_m #(.N(N16)) u16m (.a(a16), .b(b16), .cin(c16), .s(s16m), .cout(co16m));
  integer k, bad;
  reg [N4:0] e4; reg [N16:0] e16;
  initial begin
    bad = 0;
    for (k = 0; k < 512; k = k + 1) begin
      a4 = k[3:0]; b4 = k[7:4]; c4 = k[8]; #1;
      e4 = a4 + b4 + c4;
      if ({co4, s4} !== e4 || {co4m, s4m} !== e4) begin bad = bad + 1; $display("BAD4 %0d %b %b %b -> %b %b / %b %b exp %b", k, a4, b4, c4, co4, s4, co4m, s4m, e4); end
    end
    for (k = 0; k < 3000; k = k + 1) begin
      a16 = $random; b16 = $random; c16 = $random; #1;
      e16 = a16 + b16 + c16;
      if ({co16, s16} !== e16 || {co16m, s16m} !== e16) begin bad = bad + 1; $display("BAD16 %0d", k); end
    end
    a16 = 16'hFFFF; b16 = 16'h0000; c16 = 1'b1; #1; if ({co16, s16} !== 17'h10000 || {co16m, s16m} !== 17'h10000) bad = bad + 1;
    a16 = 16'h0000; b16 = 16'h0000; c16 = 1'b1; #1; if ({co16, s16} !== 17'h00001) bad = bad + 1;
    $display("RESULT bad=%0d", bad);
    $finish;
  end
endmodule
