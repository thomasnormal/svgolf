// expect: unproved
// A never-reset state register s (three loaded states and a hold for the fourth value) read only by
// comparisons with constants whose xor is 1 for every value of s (finding F2 of the 2026-11-06 adversarial
// round): in ls-sv the design is the counter from every power-up. Yosys's fsm pass recoded s one-hot over the
// three states it found (three flops), and from a power-up outside the one-hot set (all zeros among them) the
// netlist held q at 200, so the never-loaded rule refused every mapped FSM. The clocked flow now runs
// `synth -nofsm` (decided 2026-11-06): no flip-flop is re-encoded, the never-loaded rule passes the design,
// and the netlist is the design's from every power-up (MEASURED: the scored netlist from five forced
// power-ups and ls-sv from five, every cycle).
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
  logic inc;
  always_ff @(posedge clk)
    case (s)
      2'd0: s <= 2'd1;
      2'd1: s <= 2'd2;
      2'd2: s <= 2'd0;
      default: s <= s;
    endcase
  always_comb inc = !(q == 200) | ((s == 2'd0) ^ (s == 2'd1) ^ (s == 2'd2) ^ (s == 2'd3));
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
