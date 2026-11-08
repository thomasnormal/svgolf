// svGolf task `add`: a carry-select adder with 6-bit blocks, for every N >= 1.
// Q = N / 6 carry-select blocks: block j computes its carries twice, by two ripple chains in
// row j of c0 (block carry-in 0) and c1 (block carry-in 1); row j of cs picks one by the block
// carry cb[j] (the carry into each bit of the block), and the block carries ripple through one multiplexer per block. The R = N % 6 top
// bits ripple from cb[Q] through c (c[i] is the carry INTO bit i; cout = c[N]).
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  localparam integer Q = N / 6;
  localparam integer R = N % 6;
  logic [N-1:0] p, g;
  logic [Q:0][6:0] c0, c1;
  logic [Q:0][5:0] cs;
  logic [Q:0] cb;
  logic [N:0] c;
  genvar i, j, t;
  // the module-level assigns: block carry 0, the unused row Q of c0, c1, cs (every declared bit
  // is driven), the carry into the tail, the carry out
  assign cb[0] = cin;
  assign c0[Q] = 7'b0;
  assign c1[Q] = 7'b0;
  assign cs[Q] = 6'b0;
  assign c[6*Q] = cb[Q];
  assign cout = c[N];
  generate
    for (i = 0; i < N; i++) begin : g_pg
      assign p[i] = a[i] ^ b[i];
      assign g[i] = a[i] & b[i];
    end
    for (j = 0; j < Q; j++) begin : g_blk
      assign c0[j][0] = 1'b0;
      assign c1[j][0] = 1'b1;
      for (t = 0; t < 6; t++) begin : g_rip
        assign c0[j][t+1] = g[6*j+t] | (p[6*j+t] & c0[j][t]);
        assign c1[j][t+1] = g[6*j+t] | (p[6*j+t] & c1[j][t]);
        assign cs[j][t] = cb[j] ? c1[j][t] : c0[j][t];
      end
      assign cb[j+1] = cb[j] ? c1[j][6] : c0[j][6];
    end
    for (t = 0; t < R; t++) begin : g_tail
      assign c[6*Q+t+1] = g[6*Q+t] | (p[6*Q+t] & c[6*Q+t]);
    end
    for (j = 0; j < Q; j++) begin : g_sblk
      for (t = 0; t < 6; t++) begin : g_s
        assign s[6*j+t] = p[6*j+t] ^ cs[j][t];
      end
    end
    for (t = 0; t < R; t++) begin : g_stail
      assign s[6*Q+t] = p[6*Q+t] ^ c[6*Q+t];
    end
  endgenerate
endmodule
