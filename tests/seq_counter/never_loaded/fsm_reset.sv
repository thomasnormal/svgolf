// expect: unproved
// The state register s has a reset, and a never-reset register r samples, every cycle, the xor of the four
// comparisons of s with constants (1 for every value of s): in ls-sv r is 1 from the first edge on, from every
// power-up, and the design is the counter. Yosys's fsm pass recoded s one-hot, and from a power-up outside the
// one-hot set the reset edge loaded r with 0 and the first count after the reset added 0 (the netlist ended at
// 209 where the counter was at 210): a reset on the state register did not repair the recode. The clocked flow
// now runs `synth -nofsm` (decided 2026-11-06): the never-loaded rule passes the design, and the netlist is the
// design's from every power-up (MEASURED, as for fsm_unreset.sv).
// Until 2026-11-07 the post-synthesis check refused it, failing closed: Verilator's lint (every warning fatal)
// stopped on UNDRIVEN bits of a dead wire the `$pmux` techmap of the `case` left in the scored netlist
// (`\_N_.B_AND_S`, read by no cell), the over-rejection the review's section 11.3 records for a techmapped
// divider (section 12.2). The clocked flow's last clean-up is now `opt_clean -purge` (decided 2026-11-07), which
// removes that wire: the design passes every stage but the proof (MEASURED 2026-11-07, same gates as before).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic [1:0] s;
  logic r;
  always_ff @(posedge clk)
    if (rst) s <= 2'd0;
    else
      case (s)
        2'd0: s <= 2'd1;
        2'd1: s <= 2'd2;
        2'd2: s <= 2'd0;
        default: s <= s;
      endcase
  always_ff @(posedge clk) r <= (s == 2'd0) ^ (s == 2'd1) ^ (s == 2'd2) ^ (s == 2'd3);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + {{(N-1){1'b0}}, r};
  end
endmodule
