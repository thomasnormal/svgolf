// WP-I probe: a recursive module (XOR reduction by halves) instantiated from a non-recursive top.
// The default N = 8 lies on the RECURSIVE branch, so slang binds the two child instances.
module xr #(parameter int N = 8) (input logic [N-1:0] a, output logic y);
  if (N == 1) begin : g_leaf
    assign y = a[0];
  end else begin : g_node
    logic yl, yr;
    xr #(.N(N/2)) l (.a(a[N/2-1:0]), .y(yl));
    xr #(.N(N-N/2)) r (.a(a[N-1:N/2]), .y(yr));
    assign y = yl ^ yr;
  end
endmodule
module top (input logic [7:0] a, output logic y);
  xr #(.N(8)) u (.a(a), .y(y));
endmodule
