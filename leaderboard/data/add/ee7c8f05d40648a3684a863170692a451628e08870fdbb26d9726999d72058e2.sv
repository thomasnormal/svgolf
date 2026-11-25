// svGolf task `add`: ripple-carry adder with direct NAND-majority carries on bits 0 and 1,
// eliminating the XOR propagate gate from the start of the carry chain.
// Derived from tasks/add/reference/add_n.sv (record 710c45899359).
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N-1:0] p, g;
  logic [N:0] c;
  assign c[0] = cin;
  assign cout = c[N];
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign p[i] = a[i] ^ b[i];
      assign g[i] = a[i] & b[i];
      if (i < 2) begin : g_lo
        assign c[i+1] = ~(~(a[i] & b[i]) & ~((a[i] & c[i]) | (b[i] & c[i])));
      end else begin : g_hi
        assign c[i+1] = g[i] | (p[i] & c[i]);
      end
      assign s[i] = p[i] ^ c[i];
    end
  endgenerate
endmodule
