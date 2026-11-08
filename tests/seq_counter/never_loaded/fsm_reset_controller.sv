// expect: unproved
// An ordinary reset controller (the independent review of 2026-11-06): a 2-bit state s reset to 0, its three
// reached states decoded by `case (s)`, read as `s != 2'd3` beside a reset q. From the first reset on s is never
// 3, so q counts every cycle with en. Every reader compares the whole register with a constant, so Yosys's fsm
// pass mapped it ("Mapping FSM") and the never-loaded rule refused a correct design. The clocked flow now runs
// `synth -nofsm` (decided 2026-11-06): s keeps its own two flip-flops, the never-loaded rule passes the design,
// and the netlist is the design's from every power-up (MEASURED: the scored netlist from five forced power-ups
// and ls-sv from five agree at every cycle).
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
  always_ff @(posedge clk) begin
    if (rst) s <= 2'd0;
    else case (s)
      2'd0: s <= 2'd1;
      2'd1: s <= en ? 2'd2 : 2'd1;
      2'd2: s <= 2'd1;
      default: s <= 2'd0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst)                  q <= '0;
    else if (en && s != 2'd3) q <= q + 1'b1;
  end
endmodule
