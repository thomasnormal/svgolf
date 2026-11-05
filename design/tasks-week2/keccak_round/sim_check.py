"""Simulates reference/*.sv (iverilog, -g2012) against oracle.py on random + golden vectors, several W.
usage: python3 sim_check.py reference/keccak_round.sv [more.sv ...]   (needs iverilog)"""
import json, os, random, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oracle import oracle

def run(sv, W, rows):
    n = len(rows)
    tb = f"""
module tb;
  logic [24:0][{W}-1:0] a; logic [{W}-1:0] rc; wire [24:0][{W}-1:0] y;
  keccak_round #(.W({W})) dut(.a(a), .rc(rc), .y(y));
  integer fd, i, r; reg [25*{W}-1:0] ta; reg [{W}-1:0] trc;
  initial begin
    fd = $fopen("in.txt", "r");
    for (i = 0; i < {n}; i = i + 1) begin
      r = $fscanf(fd, "%h %h\\n", ta, trc); a = ta; rc = trc; #1;
      $display("Y %h", y);
    end
    $finish;
  end
endmodule
"""
    with tempfile.TemporaryDirectory() as d:
        open(f"{d}/tb.sv", "w").write(tb)
        open(f"{d}/in.txt", "w").write("".join(f"{a:x} {rc:x}\n" for a, rc in rows))
        subprocess.run(["iverilog", "-g2012", "-o", f"{d}/sim", f"{d}/tb.sv", os.path.abspath(sv)], check=True)
        out = subprocess.run(["vvp", f"{d}/sim"], cwd=d, capture_output=True, text=True, check=True).stdout.splitlines()
    return [int(l.split()[1], 16) for l in out if l.startswith("Y ")]

if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    gold = json.load(open(os.path.join(here, "vectors.json")))["rows"]
    rnd = random.Random(7)
    for sv in sys.argv[1:]:
        tot = 0
        for W in (1, 2, 3, 4, 5, 8, 16, 32, 64):
            rows = [(rnd.getrandbits(25 * W), rnd.getrandbits(W)) for _ in range(40)]
            rows += [(r["a"], r["rc"]) for r in gold if r["W"] == W]
            got = run(sv, W, rows)
            for (a, rc), g in zip(rows, got):
                exp = oracle({"W": W}, {"a": a, "rc": rc})["y"]
                assert g == exp, (sv, W, hex(a), hex(rc), hex(g), hex(exp))
            tot += len(rows)
        print(os.path.basename(sv), "OK,", tot, "vectors, W in {1,2,3,4,5,8,16,32,64}")
