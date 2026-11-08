// Measures, on the ADAPTED designs, the reactive properties a task statement would carry:
// mutual exclusion, no spurious grant, grant => ready, work conservation, and the worst wait
// (grants to others while a held request waits). Requests follow the AXI/TL rule: once raised,
// held until granted. Stimulus: xorshift32.
module tb_props;
  parameter int N = 4;
  parameter int DUT = 0;   // 0: prim_arbiter_tree (OpenTitan), 1: cc_rr_arb_tree (pulp)
  parameter int RDY_PCT = 75;
  localparam int IW = (N > 1) ? $clog2(N) : 1;
  logic clk = 0, rst;
  logic [N-1:0] req, gnt; logic ready, valid; logic [IW-1:0] idx;
  logic [N-1:0][0:0] din;
  logic [0:0] dout;
  logic [31:0] xs = 32'h1234567;
  function automatic logic [31:0] rnd();
    xs = xs ^ (xs << 13); xs = xs ^ (xs >> 17); xs = xs ^ (xs << 5);
    return xs;
  endfunction
  if (DUT == 0) begin : g0
    prim_arbiter_tree #(.N(N), .DW(1)) d (.clk_i(clk), .rst_i(rst), .req_chk_i(1'b1), .req_i(req),
      .data_i(din), .gnt_o(gnt), .idx_o(idx), .valid_o(valid), .data_o(dout), .ready_i(ready));
  end else begin : g1
    cc_rr_arb_tree #(.NumIn(N), .DataWidth(1)) d (.clk_i(clk), .rst_i(rst), .clr_i(1'b0), .rr_i('0),
      .req_i(req), .gnt_o(gnt), .data_i(din), .req_o(valid), .gnt_i(ready), .data_o(dout), .idx_o(idx));
  end
  integer cyc, k, bad_mutex, bad_spur, bad_rdy, bad_wc, bad_idx, maxwait, ngr;
  integer wait_[N];
  logic [N-1:0] g;
  logic pv = 0; logic [IW-1:0] pidx = 0; integer bad_lock = 0;
  initial begin
    bad_mutex = 0; bad_spur = 0; bad_rdy = 0; bad_wc = 0; bad_idx = 0; maxwait = 0; ngr = 0;
    for (k = 0; k < N; k++) wait_[k] = 0;
    rst = 1; req = '0; ready = 0; din = '0;
    #1 clk = 1; #1 clk = 0; rst = 0;
    for (cyc = 0; cyc < 50000; cyc++) begin
      for (k = 0; k < N; k++) if (!req[k] && rnd() % 2 == 0) req[k] = 1'b1;
      ready = (rnd() % 100) < RDY_PCT;
      #1;
      if (!$onehot0(gnt)) bad_mutex++;
      if ((gnt & ~req) != '0) bad_spur++;
      if (|gnt && !ready) bad_rdy++;
      if (ready && |req && !(|gnt)) bad_wc++;
      if (|gnt && !gnt[idx]) bad_idx++;
      g = gnt;   // sample before the edge
      if (pv && |req && idx != pidx) bad_lock++;
      pv = valid && !ready; pidx = idx;
      clk = 1; #1 clk = 0;
      for (k = 0; k < N; k++) begin
        if (req[k] && g[k]) begin
          if (wait_[k] > maxwait) maxwait = wait_[k];
          wait_[k] = 0; req[k] = 1'b0;
        end else if (req[k] && |g) wait_[k] = wait_[k] + 1;
      end
      if (|g) ngr++;
    end
    $display("DUT=%0d N=%0d ready=%0d%% grants=%0d mutex_viol=%0d spurious=%0d gnt_wo_ready=%0d not_work_conserving=%0d idx_mismatch=%0d max_wait_grants=%0d decision_changed_under_backpressure=%0d",
             DUT, N, RDY_PCT, ngr, bad_mutex, bad_spur, bad_rdy, bad_wc, bad_idx, maxwait, bad_lock);
    $finish;
  end
endmodule
