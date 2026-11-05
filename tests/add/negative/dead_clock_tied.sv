// NEGATIVE (the dead_clock.sv variant with the clock tied to 1'b0): a
// correct ripple adder computes the sum into internal signals, and the
// outputs are REGISTERED on a clock that is constant 0. ls-sv runs every
// always_ff once per cycle whatever its clock holds, so every ls-sv snapshot
// carries the right {cout, s}; every simulator and Yosys see a clock that
// never rises (s and cout stay x, and Yosys scores the design at 0 GE). The
// statement's `Unclocked` conjunct rejects it: refuted in Refute.lean
// (deadClockTied_refuted) at N = 1.
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic         clk;
  logic [N-1:0] sc;
  logic [N:0]   c;
  assign clk  = 1'b0;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign sc[i]  = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
  endgenerate
  always_ff @(posedge clk) begin
    s    <= sc;
    cout <= c[N];
  end
endmodule
