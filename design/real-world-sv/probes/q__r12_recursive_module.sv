module rec #(parameter int W = 8) (input logic [W-1:0] x, output logic y);
  if (W == 1) begin : base
    assign y = x[0];
  end else begin : step
    logic yl, yh;
    rec #(.W(W/2)) l (.x(x[W/2-1:0]), .y(yl));
    rec #(.W(W - W/2)) h (.x(x[W-1:W/2]), .y(yh));
    assign y = yl ^ yh;
  end
endmodule
module t #(parameter int N = 16) (input logic [N-1:0] a, output logic y);
  rec #(.W(N)) u (.x(a), .y(y));
endmodule
