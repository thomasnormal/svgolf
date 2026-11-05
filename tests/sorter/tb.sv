// Reactive C8 driver for `sorter` (sim.py writes stim.txt and checks the log; the claim is checked in
// Python from the log alone). Entry c: the inputs are set, the clock edge samples them, and the
// outputs are printed 1 ns later (snapshot c). Per transaction line of stim.txt:
//   gap abort nfree x_0 .. x_{N-1} free_0 .. free_{nfree-1}
// Idle (StreamTask.Idle) is observed: the next gap starts after the snapshot showing the N-th
// output since the last start, or after LAT+4 entries past the last input (a FORCED start, which
// sim.py treats as the end of the horizon). abort = k >= 0: reset for 1 entry after k inputs.
`timescale 1ns / 1ps
module tb;
  parameter int N = 8, W = 8, LAT = 16;
  logic clk = 1'b0, rst = 1'b1, start = 1'b0, in_valid = 1'b0;
  logic [W-1:0] in_data = '0;
  logic out_valid;
  logic [W-1:0] out_data;
  sorter #(.N(N), .W(W)) dut (.clk(clk), .rst(rst), .start(start), .in_valid(in_valid),
                              .in_data(in_data), .out_valid(out_valid), .out_data(out_data));
  integer fd, c, nout, g, ab, nf, fi, j, wt, r, first;
  integer xs [0:4095];
  integer fr [0:16383];

  task automatic entry(input logic r_, s_, v_, input integer d_);
    rst = r_; start = s_; in_valid = v_; in_data = d_[W-1:0];
    #5 clk = 1'b1;
    #1 $display("E %0d %b %b %b %h %b %h", c, rst, start, in_valid, in_data, out_valid, out_data);
    if (out_valid === 1'b1) nout = nout + 1;
    #4 clk = 1'b0;
    c = c + 1;
  endtask

  task automatic idle();
    entry(1'b0, 1'b0, 1'b0, fr[fi % nf]);
    fi = fi + 1;
  endtask

  initial begin
    c = 0; nout = 0; first = 1;
    fd = $fopen("stim.txt", "r");
    entry(1'b1, 1'b0, 1'b0, 0);                               // reset, 1 entry: C1's least
    while ($fscanf(fd, "%d %d %d", g, ab, nf) == 3) begin
      for (j = 0; j < N; j++) r = $fscanf(fd, "%d", xs[j]);
      for (j = 0; j < nf; j++) r = $fscanf(fd, "%d", fr[j]);
      fi = 0;
      if (!first) begin                                       // wait for Idle
        wt = 0;
        while (nout < N && wt < LAT + 4) begin idle(); wt = wt + 1; end
        if (nout < N) $display("FORCED %0d", c);
      end
      first = 0;
      for (j = 0; j < g; j++) idle();
      nout = 0;                                               // outputs count from snapshot s on
      entry(1'b0, 1'b1, 1'b0, fr[fi % nf]); fi = fi + 1;        // start
      for (j = 0; j < N && !(j > ab && ab >= 0); j++)
        if (j == ab) begin
          entry(1'b1, 1'b0, 1'b0, 0);
          first = 1;
        end else
          entry(1'b0, 1'b0, 1'b1, xs[j]);
    end
    wt = 0;
    while (wt < LAT + 2 * N + 4) begin idle(); wt = wt + 1; end
    $finish;
  end
endmodule
