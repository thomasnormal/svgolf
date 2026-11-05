// svGolf attack (add): a correct ripple sum behind a case on cin with a `1'bz`
// item. ls-sv and 4-state simulators (Icarus 12, measured 10/28) compare case
// items by ===: cin is never z, so the
// default arm runs and s/cout are the sum. Yosys reads the z item as a don't-care
// match and drives s and cout with x: the scored netlist is 0 GE. Refused by the
// source gate (an x/z literal digit); before that rule it passed every stage up to
// postsynth, which rejects it on every vector (the `postsynth_alone` row).
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N-1:0] sr;
  logic         cr;
  logic [N:0] c;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign sr[i]  = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
  endgenerate
  assign cr = c[N];
  always_comb
    case (cin)
      1'bz: begin s = '0; cout = 1'b0; end
      default: begin s = sr; cout = cr; end
    endcase
endmodule
