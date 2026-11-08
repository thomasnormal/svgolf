// Testbench for the task `arbiter` (tasks/arbiter/Spec.lean): an executable reading of the
// statement, by simulation (Icarus, 4-state). Not a proof. sim.py builds it per design and point.
//
// The protocol is ls-sv's: entry c sets rst and req, the edge of cycle c samples them, and the
// SNAPSHOT c is read 1 ns after the edge with the entry still applied. Checked per snapshot:
//   G0  a reset entry's snapshot shows gnt = 0
//   G1  at most one grant          G2  gnt only to requesters of the same entry
//   G3  some grant whenever req != 0
//   G4  no client requests at K+1 = N consecutive entries of a segment without a grant among them
// and, beyond the snapshots, the SILICON view `MooreOut` guarantees: when the next entry's req is
// applied, gnt before the next edge still shows the snapshot's value (MO). A Mealy design fails MO.
//
// Stimulus: xorshift32. MODE 0: each client requests at random every entry (75%), MODE 1: a raised
// request is held until a snapshot grants it (the AXI rule), MODE 2: everyone requests always, MODE 3
// (2026-11-07): sparse, one random client alone or nobody, and a reset every 16 entries on average, so the
// first entries after a release often hold one client alone (the case that kills mutant m040 at N = 5, 8).
// Every entry of modes 0 to 2 is a reset with probability 1/256 (a new segment starts at the next release).
//
// POWER-UP (2026-11-07): with POWERUP defined, the DUT is sim.py's copy of the design at N, read by Yosys
// (`proc`) with every flip-flop and every undriven variable given a 0/1 power-up value (`setundef -undriven
// -init`: all zeros in mode 0, a seeded random state in the others), the statement's runs (txtask-v2 rule 2:
// from every 0/1 power-up state). The statement's rule 3 (XSafe) makes every value known, and a 4-state x
// start was Icarus's resolution, which killed the correct mutant m067 (its mask has no reset), so no CHECK
// asks that gnt is known. XK is a SELF-CHECK of the harness instead: under POWERUP it counts every snapshot
// and every pre-edge sample whose gnt is unknown, which a correct 0/1 power-up of an x-safe design cannot
// give. It guards the power-up itself (the review's F1, 2026-11-07): when a power-up value is lost, an x on
// gnt fires none of G0 to G4 and MO (`==`/`!=` on x give x, `if (x)` is false), so a wrong design passed.
// Without POWERUP (the third-party --axis and --ot sources), the design runs from Icarus's own x start and
// XK stays 0.
`timescale 1ns / 1ps
module tb;
  parameter int N = 4;
  parameter int MODE = 0;
  parameter int CYCLES = 20000;
  parameter int SEED = 1;
  localparam int K = N - 1;
  logic clk = 1'b0, rst = 1'b1;
  logic [N-1:0] req = '0;
  logic [N-1:0] gnt, snap;
`ifdef AXIS
  // verilog-axis arbiter.v (alexforencich), round-robin, not blocking, MSB priority
  logic gv; logic [((N > 1) ? $clog2(N) : 1)-1:0] ge;
  arbiter #(.PORTS(N), .ARB_TYPE_ROUND_ROBIN(1), .ARB_BLOCK(0), .ARB_BLOCK_ACK(0),
            .ARB_LSB_HIGH_PRIORITY(0))
    dut (.clk(clk), .rst(rst), .request(req), .acknowledge('0), .grant(gnt), .grant_valid(gv),
         .grant_encoded(ge));
`elsif OTREG
  // OpenTitan prim_arbiter_tree (adapted, Mealy) behind one output register (ready = 1)
  logic [N-1:0] g_c; logic v_c; logic [((N > 1) ? $clog2(N) : 1)-1:0] i_c;
  logic [N-1:0][0:0] din = '0; logic [0:0] dout;
  prim_arbiter_tree #(.N(N), .DW(1)) core (.clk_i(clk), .rst_i(rst), .req_chk_i(1'b1), .req_i(req),
    .data_i(din), .gnt_o(g_c), .idx_o(i_c), .valid_o(v_c), .data_o(dout), .ready_i(1'b1));
  always_ff @(posedge clk) gnt <= rst ? '0 : g_c;
`elsif OTRAW
  // the same Mealy core with no output register (outside the kind: fails MO)
  logic v_c; logic [((N > 1) ? $clog2(N) : 1)-1:0] i_c;
  logic [N-1:0][0:0] din = '0; logic [0:0] dout;
  prim_arbiter_tree #(.N(N), .DW(1)) core (.clk_i(clk), .rst_i(rst), .req_chk_i(1'b1), .req_i(req),
    .data_i(din), .gnt_o(gnt), .idx_o(i_c), .valid_o(v_c), .data_o(dout), .ready_i(1'b1));
`elsif POWERUP
  arbiter dut (.clk(clk), .rst(rst), .req(req), .gnt(gnt));      // elaborated at N by sim.py's Yosys run
`else
  arbiter #(.N(N)) dut (.clk(clk), .rst(rst), .req(req), .gnt(gnt));
`endif
  logic [31:0] xs;
  function automatic logic [31:0] rnd();
    xs = xs ^ (xs << 13); xs = xs ^ (xs >> 17); xs = xs ^ (xs << 5);
    return xs;
  endfunction
  integer c, k, seg, b_g0, b_g1, b_g2, b_g3, b_g4, b_mo, b_xk, maxmiss, grants;
  integer miss [N];
  logic r_now;
  logic [N-1:0] req_n;
  initial begin
    xs = 32'h9E3779B9 ^ SEED;
    b_g0 = 0; b_g1 = 0; b_g2 = 0; b_g3 = 0; b_g4 = 0; b_mo = 0; b_xk = 0; maxmiss = 0; grants = 0;
    seg = 0; snap = 'x;
    for (k = 0; k < N; k++) miss[k] = 0;
    for (c = 0; c < CYCLES; c++) begin
      // entry c, chosen from the past only (snapshot c-1)
      r_now = (c < 2) || (rnd() % (MODE == 3 ? 16 : 256) == 0);
      for (k = 0; k < N; k++) req_n[k] = 1'b0;
      if (MODE == 3) begin
        if (rnd() % 4 != 0) req_n[rnd() % N] = 1'b1;
      end else for (k = 0; k < N; k++) begin
        if (MODE == 2) req_n[k] = 1'b1;
        else if (MODE == 1 && req[k] === 1'b1 && snap[k] !== 1'b1 && seg == 1) req_n[k] = 1'b1;
        else req_n[k] = (rnd() % 4) != 0;
      end
      rst = r_now; req = req_n;
      #1;
      // MO: the previous snapshot's grant is still on the wire before this edge
      if (seg == 1 && gnt !== snap) b_mo++;
`ifdef POWERUP
      if ($isunknown(gnt)) b_xk++;        // XK, the harness self-check: the pre-edge sample
`endif
      #4 clk = 1'b1;
      #1 snap = gnt;
`ifdef POWERUP
      if ($isunknown(gnt)) b_xk++;        // XK: the snapshot
`endif
      if (r_now) begin
        if (gnt !== '0) b_g0++;
        seg = 1;
        for (k = 0; k < N; k++) miss[k] = 0;
      end else begin
        if (!$onehot0(gnt)) b_g1++;
        if ((gnt & ~req) != '0) b_g2++;
        if (req != '0 && gnt == '0) b_g3++;
        if (gnt != '0) grants++;
        for (k = 0; k < N; k++) begin
          if (req[k] && !gnt[k]) miss[k] = miss[k] + 1; else miss[k] = 0;
          if (miss[k] > maxmiss) maxmiss = miss[k];
          if (miss[k] > K) begin b_g4++; miss[k] = 0; end
        end
      end
      #4 clk = 1'b0;
    end
    $display("RESULT N=%0d MODE=%0d cycles=%0d grants=%0d G0=%0d G1=%0d G2=%0d G3=%0d G4=%0d MO=%0d XK=%0d maxmiss=%0d",
             N, MODE, CYCLES, grants, b_g0, b_g1, b_g2, b_g3, b_g4, b_mo, b_xk, maxmiss);
    $finish;
  end
endmodule
