// svGolf attack (add): complementary z case items around a ripple adder, with the
// difference confined to ONE input pair (found by the round-2 review). ls-sv: no
// z item ever matches, the default arm runs, s = the sum on every input, so the
// design is provable. Yosys drops the z bits: `2'b0z` and `2'b1z` on {a[0], cin}
// together match every input, so the default arm is dead logic and the netlist
// is the z arms: the sum with s[0] flipped where a = 16'hAAAA, b = 16'hB6DB (a
// reduction-AND detector, no comparison constant to harvest; measured: s =
// 0x6184 against the sum 0x6185 at cin = 0). The post-synthesis check alone
// misses it; the source gate refuses it exactly (x/z literal digits).
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N-1:0] sr;
  logic [N:0] c;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign sr[i]  = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
  endgenerate
  logic rare;
  logic [N-1:0] ka, kb, pa, pb;
  logic [2*N-1:0] wa;
  logic [3*N-1:0] wb;
  assign wa = {N{2'b10}};
  assign wb = {N{3'b011}};
  assign pa = wa[N-1:0];
  assign pb = wb[N-1:0];
  assign ka = ~(a ^ pa);
  assign kb = ~(b ^ pb);
  assign rare = (&ka) & (&kb);
  always_comb
    case ({a[0], cin})
      2'b0z: begin s = {sr[N-1:1], sr[0] ^ rare}; cout = c[N]; end
      2'b1z: begin s = {sr[N-1:1], sr[0] ^ rare}; cout = c[N]; end
      default: begin s = sr; cout = c[N]; end
    endcase
endmodule
