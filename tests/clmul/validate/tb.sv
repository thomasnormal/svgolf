// Testbench for task `clmul`: p must be the carry-less (GF(2)[x]) product of a and b on 2N-1 bits.
// The expected value is computed by shift-and-XOR on the whole word (one XOR of `a << i` per set bit of b),
// a different route from the design's per-bit array (and from oracle.py, which is Python).
module tb;
  parameter int N = 4;
  parameter int EXH = 1;          // 1: exhaustive; 0: random
  parameter int NRAND = 100000;
  logic [N-1:0] a, b;
  logic [2*N-2:0] p, want, aw;
  longint errs = 0, cnt = 0;
  clmul_n #(.N(N)) dut (.a(a), .b(b), .p(p));
  task automatic check1;
    #1;
    aw = a;
    want = '0;
    for (int i = 0; i < N; i++)
      if (b[i]) want = want ^ (aw << i);
    cnt++;
    if (p !== want) begin
      errs++;
      if (errs < 5) $display("MISMATCH N=%0d a=%0h b=%0h p=%0h want=%0h", N, a, b, p, want);
    end
  endtask
  initial begin
    if (EXH) begin
      for (longint x = 0; x < (64'd1 << N); x++)
        for (longint y = 0; y < (64'd1 << N); y++) begin
          a = x[N-1:0]; b = y[N-1:0]; check1();
        end
    end else begin
      // corners first
      a = '0; b = '0; check1();
      a = '1; b = '1; check1();
      a = '1; b = '0; check1();
      a = '0; b = '1; check1();
      a = '1; b = 1; check1();
      for (int k = 0; k < N; k++) begin   // walking ones against the all-ones word
        a = '0; a[k] = 1'b1; b = '1; check1();
        a = '1; b = '0; b[k] = 1'b1; check1();
      end
      for (int k = 0; k < NRAND; k++) begin
        a = {$urandom, $urandom, $urandom};
        b = {$urandom, $urandom, $urandom};
        check1();
      end
    end
    $display("RESULT N=%0d EXH=%0d vectors=%0d errors=%0d", N, EXH, cnt, errs);
    $finish;
  end
endmodule
