// The environment of task `gemm`: the external memory, the activation source, the result sink and the job source,
// around one `gemm` design (or its scored netlist). It drives the stimulus files oracle.py wrote and records every
// transfer and every change of the design's control outputs in a trace, which oracle.py judges (`check_trace`).
//
//   +dir=DIR        the directory of the stimulus files and of the trace (trace.txt)
//   +njobs=K        jobs in jobs.hex            +nstall=K   words in stall.hex (read cyclically)
//   +nybeats=K      result beats to wait for    +maxcyc=K   give up after K cycles (`T` line)
// Compile with +define+GEMM_NETLIST around a gate netlist of the design (its parameters are fixed by the synthesis).
//
// Files (hex, one word per line): jobs.hex {x beats[32], image beats[32], image base[32], hi, lo, zp, shift[8],
// mul, batch, lgn[8]}; mem.hex, the images back to back, one beat per line; x.hex, the activation beats;
// stall.hex, bit k pauses channel k (job_valid, rq_ready, rd_valid, x_valid, y_ready) in that cycle.
//
// The memory: one burst at a time. A request is accepted only when no burst is outstanding; the first beat is
// valid LAT cycles after the request's transfer (later when paused), the others follow at full rate; a burst reads
// the image of the job that was current when its request was accepted (the image changes in the cycle after a job
// is accepted). While rd_valid, x_valid or job_valid is 0 the lines of that channel carry garbage.
module gemm_tb #(
  parameter int LGE = 2,
  parameter int LAT = 3,
  parameter int MEMBEATS = 1 << 16,
  parameter int XBEATS = 1 << 16,
  parameter int MAXJOBS = 64,
  parameter int MAXSTALL = 1 << 14
) (
  input logic clk
);
  localparam int E = 1 << LGE;
  localparam int MEMW = 16 * E;

  logic            rst;
  logic            job_valid, job_ready;
  logic [3:0]      job_lgn;
  logic [15:0]     job_batch, job_mul, job_zp, job_lo, job_hi;
  logic [5:0]      job_shift;
  logic            rq_valid, rq_ready;
  logic [31:0]     rq_addr;
  logic [23:0]     rq_len;
  logic            rd_valid, rd_ready;
  logic [MEMW-1:0] rd_data;
  logic            x_valid, x_ready;
  logic [MEMW-1:0] x_data;
  logic            y_valid, y_ready;
  logic [15:0]     y_vec;
  logic [4:0]      y_row;
  logic [MEMW-1:0] y_data;

`ifdef GEMM_NETLIST
  gemm dut (.*);                                  // a netlist: synthesized at this point, no parameters left
`else
  gemm #(.LGE(LGE), .LAT(LAT)) dut (.*);
`endif

  logic [191:0]    jobs [0:MAXJOBS-1];
  logic [MEMW-1:0] mem [0:MEMBEATS-1];
  logic [MEMW-1:0] xs [0:XBEATS-1];
  logic [7:0]      stall [0:MAXSTALL-1];

  string  dir;
  integer fd, njobs, nstall, nybeats, maxcyc;
  integer cyc, jnext, jcur, xnext, xlimit, ygot, tail, done;
  integer b_act, b_wait, b_left, b_ptr;          // the outstanding burst
  integer img_base, img_size, img_base_n, img_size_n;
  logic [63:0] lfsr;
  logic [7:0]  st;
  logic [191:0] jw;
  // last cycle's view of the design's outputs (the hold rule and the change records)
  logic        p_first, p_jr, p_rqv, p_rdr, p_xr, p_yv, p_rqr, p_yr;
  logic [31:0] p_addr;
  logic [23:0] p_len;
  logic [15:0] p_vec;
  logic [4:0]  p_row;
  logic [MEMW-1:0] p_ydata;
  // the environment's next values, driven with nonblocking assignments at the end of the block (no race with the design)
  logic        e_rst, e_jv, e_rqr, e_rdv, e_xv, e_yr;
  logic [MEMW-1:0] e_rdd, e_xd;
  logic [3:0]  e_lgn;
  logic [15:0] e_batch, e_mul, e_zp, e_lo, e_hi;
  logic [5:0]  e_shift;

  function automatic logic [MEMW-1:0] garbage(input logic [63:0] s);
    logic [MEMW-1:0] g;
    for (int k = 0; k < MEMW; k += 16) g[k +: 16] = s[15:0] ^ 16'(k * 16'h9E37) ^ s[31:16];
    return g;
  endfunction

  initial begin
    if (!$value$plusargs("dir=%s", dir)) dir = ".";
    if (!$value$plusargs("njobs=%d", njobs)) njobs = 0;
    if (!$value$plusargs("nstall=%d", nstall)) nstall = 1;
    if (!$value$plusargs("nybeats=%d", nybeats)) nybeats = 0;
    if (!$value$plusargs("maxcyc=%d", maxcyc)) maxcyc = 100000;
    $readmemh({dir, "/jobs.hex"}, jobs);
    $readmemh({dir, "/mem.hex"}, mem);
    $readmemh({dir, "/x.hex"}, xs);
    $readmemh({dir, "/stall.hex"}, stall);
    fd = $fopen({dir, "/trace.txt"}, "w");
    cyc = 0; jnext = 0; jcur = -1; xnext = 0; xlimit = 0; ygot = 0; tail = 0; done = 0;
    b_act = 0; b_wait = 0; b_left = 0; b_ptr = 0;
    img_base = 0; img_size = 0; img_base_n = 0; img_size_n = 0;
    lfsr = 64'h1234_5678_9ABC_DEF1;
    rst = 1'b1;
    job_valid = 1'b0; rq_ready = 1'b0; rd_valid = 1'b0; x_valid = 1'b0; y_ready = 1'b0;
    job_lgn = '0; job_batch = '0; job_mul = '0; job_shift = '0; job_zp = '0; job_lo = '0; job_hi = '0;
    rd_data = '0; x_data = '0;
    p_first = 1'b1;
  end

  always @(posedge clk) begin
    if (!done) begin
      e_rst = rst; e_jv = job_valid; e_rqr = rq_ready; e_rdv = rd_valid; e_xv = x_valid; e_yr = y_ready;
      e_rdd = rd_data; e_xd = x_data;
      e_lgn = job_lgn; e_batch = job_batch; e_mul = job_mul; e_shift = job_shift; e_zp = job_zp; e_lo = job_lo; e_hi = job_hi;
      st = stall[cyc % nstall];
      lfsr = {lfsr[62:0], lfsr[63] ^ lfsr[62] ^ lfsr[60] ^ lfsr[59]};
      if (!rst) begin
        // ---- what the design did in the cycle that ends at this edge
        if (!p_first) begin
          if (p_rqv && !p_rqr && !(rq_valid && rq_addr == p_addr && rq_len == p_len))
            $fwrite(fd, "E %0d the design dropped or changed a memory request before its transfer\n", cyc);
          if (p_yv && !p_yr && !(y_valid && y_vec == p_vec && y_row == p_row && y_data == p_ydata))
            $fwrite(fd, "E %0d the design dropped or changed a result beat before its transfer\n", cyc);
        end
        if (p_first || job_ready != p_jr || rq_valid != p_rqv || rd_ready != p_rdr || x_ready != p_xr
            || y_valid != p_yv || (rq_valid && (rq_addr != p_addr || rq_len != p_len))
            || (y_valid && (y_vec != p_vec || y_row != p_row)))
          $fwrite(fd, "S %0d %b%b%b%b%b %0d %0d %0d %0d\n", cyc, job_ready, rq_valid, rd_ready, x_ready, y_valid,
                  rq_valid ? rq_addr : 32'd0, rq_valid ? rq_len : 24'd0, y_valid ? y_vec : 16'd0,
                  y_valid ? y_row : 5'd0);
        p_first = 1'b0;
        p_jr = job_ready; p_rqv = rq_valid; p_rdr = rd_ready; p_xr = x_ready; p_yv = y_valid;
        p_rqr = rq_ready; p_yr = y_ready;
        p_addr = rq_addr; p_len = rq_len; p_vec = y_vec; p_row = y_row; p_ydata = y_data;

        // ---- transfers at this edge
        img_base = img_base_n; img_size = img_size_n;       // the image of the job accepted before this cycle
        if (job_valid && job_ready) begin
          $fwrite(fd, "J %0d %0d\n", cyc, jnext);
          jw = jobs[jnext];
          img_base_n = int'(jw[127:96]); img_size_n = int'(jw[159:128]);
          xlimit = xlimit + int'(jw[191:160]);
          jcur = jnext; jnext = jnext + 1;
          e_jv = 1'b0;
        end
        if (rq_valid && rq_ready) begin
          $fwrite(fd, "Q %0d %0d %0d\n", cyc, rq_addr, rq_len);
          if (rq_len == 0 || int'(rq_addr) + int'(rq_len) > img_size) begin
            $fwrite(fd, "E %0d the request (%0d beats at %0d) leaves the job's image\n", cyc, rq_len, rq_addr);
            b_left = 0;                                     // not served: the run times out
          end else begin
            b_act = 1; b_wait = LAT; b_left = int'(rq_len); b_ptr = img_base + int'(rq_addr);
          end
        end
        if (rd_valid && rd_ready) begin
          $fwrite(fd, "D %0d\n", cyc);
          e_rdv = 1'b0;
          b_left = b_left - 1; b_ptr = b_ptr + 1;
          if (b_left == 0) b_act = 0;
        end
        if (x_valid && x_ready) begin
          $fwrite(fd, "X %0d\n", cyc);
          e_xv = 1'b0;
          xnext = xnext + 1;
        end
        if (y_valid && y_ready) begin
          $fwrite(fd, "Y %0d %0d %0d %h\n", cyc, y_vec, y_row, y_data);
          ygot = ygot + 1;
        end

        // ---- what the environment drives in the next cycle
        if (!e_jv && jnext < njobs && !st[0]) begin
          jw = jobs[jnext];
          e_jv = 1'b1;
          e_lgn = jw[3:0]; e_batch = jw[23:8]; e_mul = jw[39:24]; e_shift = jw[45:40];
          e_zp = jw[63:48]; e_lo = jw[79:64]; e_hi = jw[95:80];
        end
        if (!e_jv) begin                                    // no job offered: the job lines carry garbage
          e_lgn = lfsr[3:0]; e_batch = lfsr[19:4]; e_mul = lfsr[35:20]; e_shift = lfsr[41:36];
          e_zp = lfsr[57:42]; e_lo = lfsr[47:32]; e_hi = lfsr[63:48];
        end
        if (b_act != 0 && b_wait > 0) b_wait = b_wait - 1;
        if (b_act != 0 && b_wait == 0 && !e_rdv && !st[2]) begin
          e_rdv = 1'b1;
          e_rdd = mem[b_ptr];
        end
        if (!e_rdv) e_rdd = garbage(lfsr);
        e_rqr = (b_act == 0) && !st[1];
        if (!e_xv && xnext < xlimit && !st[3]) begin
          e_xv = 1'b1;
          e_xd = xs[xnext];
        end
        if (!e_xv) e_xd = garbage({lfsr[31:0], lfsr[63:32]});
        e_yr = !st[4];

        if (ygot >= nybeats && tail == 0) tail = cyc + 64;  // every result is in: watch 64 more cycles
        if (tail != 0 && cyc >= tail) begin
          $fwrite(fd, "F %0d\n", cyc);
          $fclose(fd);
          done = 1;
          $finish;
        end
      end
      if (cyc >= maxcyc && !done) begin
        $fwrite(fd, "T %0d\n", cyc);
        $fclose(fd);
        done = 1;
        $finish;
      end
      if (cyc == 2) e_rst = 1'b0;                            // reset held for the first three cycles
      rst <= e_rst; job_valid <= e_jv; rq_ready <= e_rqr; rd_valid <= e_rdv; x_valid <= e_xv; y_ready <= e_yr;
      rd_data <= e_rdd; x_data <= e_xd;
      job_lgn <= e_lgn; job_batch <= e_batch; job_mul <= e_mul; job_shift <= e_shift; job_zp <= e_zp; job_lo <= e_lo; job_hi <= e_hi;
      cyc = cyc + 1;
    end
  end
endmodule
