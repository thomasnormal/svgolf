module addwc #(parameter int N = 4) (input logic [N-1:0] a, b, input logic cin, output logic [N-1:0] s, output logic cout);
  logic [N:0] t;
  assign t = a + b + cin;
  assign s = t[N-1:0];
  assign cout = t[N];
endmodule
