module tb;
  parameter int N = 4;
  parameter int EXH = 1;          // 1: exhaustive; 0: random
  parameter int NRAND = 100000;
  logic [N-1:0] a, b;
  logic [2*N-1:0] p, want;
  longint errs = 0, cnt = 0;
  mul_n #(.N(N)) dut (.a(a), .b(b), .p(p));
  task automatic check1;
    #1;
    want = {{N{1'b0}}, a} * {{N{1'b0}}, b};
    cnt++;
    if (p !== want) begin
      errs++;
      if (errs < 5) $display("MISMATCH N=%0d a=%0d b=%0d p=%0d want=%0d", N, a, b, p, want);
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
