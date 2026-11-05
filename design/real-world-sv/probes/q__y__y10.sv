module t #(parameter int N=8) (input logic [N-1:0] a, output logic [N-1:0] y);
  function automatic logic [N-1:0] rev(input logic [N-1:0] x);
    for (int i = 0; i < N; i++) rev[i] = x[N-1-i];
  endfunction
  assign y = rev(a);
endmodule
