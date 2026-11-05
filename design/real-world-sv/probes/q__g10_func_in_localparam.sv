module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  function automatic int lg(input int v);
    int r;
    r = 0;
    for (int k = 1; k < v; k = k * 2) r = r + 1;
    return r;
  endfunction
  localparam int L = lg(N);
  assign y = a;
endmodule
