// H2 style S2: the same loop in an automatic function called from a continuous assign.
module s2_function (
  input  logic [10:0] n, d,
  output logic [12:0] qq
);
  function automatic logic [12:0] divq(input logic [10:0] nn, input logic [10:0] dd);
    logic [11:0] rr;
    logic [12:0] q;
    rr = {1'b0, nn};
    for (int i = 12; i >= 0; i--) begin
      q[i] = (rr >= {1'b0, dd});
      rr = q[i] ? ((rr - {1'b0, dd}) << 1) : (rr << 1);
    end
    return q;
  endfunction
  assign qq = divq(n, d);
endmodule
